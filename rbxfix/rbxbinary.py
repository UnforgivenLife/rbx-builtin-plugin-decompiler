"""Minimal reader/writer for Roblox's binary model/place format (.rbxm / .rbxl).

Only the pieces needed for this tool are interpreted (INST chunks, the string
based PROP chunks); every other chunk/property is round-tripped byte for byte.

File layout:
    "<roblox!" 89 FF 0D 0A 1A 0A  | u16 version | i32 classCount | i32 instCount | 8 reserved
    chunks: char[4] name | u32 compressedLen | u32 uncompressedLen | u32 reserved | data
    (compressedLen == 0 -> raw; else LZ4 block or ZSTD frame)
"""
import struct

try:
    import lz4.block as _lz4
except ImportError:  # pragma: no cover
    _lz4 = None
try:
    import zstandard as _zstd
except ImportError:  # pragma: no cover
    _zstd = None

MAGIC = b"<roblox!\x89\xff\r\n\x1a\n"
ZSTD_MAGIC = b"\x28\xb5\x2f\xfd"

# property type ids
PT_STRING = 0x01
PT_PROTECTED_STRING = 0x1D


class RbxFormatError(Exception):
    pass


class Chunk:
    __slots__ = ("name", "data", "reserved")

    def __init__(self, name, data, reserved=0):
        self.name = name
        self.data = data
        self.reserved = reserved

    def __repr__(self):
        return "Chunk(%r, %d bytes)" % (self.name, len(self.data))


def _decompress(raw, ulen):
    if raw[:4] == ZSTD_MAGIC:
        if _zstd is None:
            raise RbxFormatError("file uses ZSTD compression; `pip install zstandard`")
        return _zstd.ZstdDecompressor().decompress(raw, max_output_size=ulen)
    if _lz4 is None:
        raise RbxFormatError("file uses LZ4 compression; `pip install lz4`")
    return _lz4.decompress(raw, uncompressed_size=ulen)


class RbxFile:
    def __init__(self):
        self.version = 0
        self.num_classes = 0
        self.num_instances = 0
        self.reserved = b"\0" * 8
        self.chunks = []

    # ------------------------------------------------------------------ io
    @classmethod
    def load(cls, path):
        with open(path, "rb") as f:
            return cls.from_bytes(f.read())

    @classmethod
    def from_bytes(cls, d):
        if not d.startswith(MAGIC):
            if d.lstrip()[:7] == b"<roblox":
                raise RbxFormatError("XML model files are not handled by this tool")
            raise RbxFormatError("not a binary Roblox file")
        self = cls()
        self.version, self.num_classes, self.num_instances = struct.unpack_from("<Hii", d, 14)
        self.reserved = d[24:32]
        p = 32
        while p < len(d):
            if p + 16 > len(d):
                raise RbxFormatError("truncated chunk header")
            name = d[p:p + 4]
            clen, ulen, res = struct.unpack_from("<III", d, p + 4)
            p += 16
            if clen == 0:
                body = d[p:p + ulen]
                p += ulen
            else:
                body = _decompress(d[p:p + clen], ulen)
                p += clen
            if len(body) != ulen:
                raise RbxFormatError("chunk %r size mismatch" % name)
            self.chunks.append(Chunk(name.rstrip(b"\0").decode("ascii", "replace"), body, res))
            if name == b"END\0":
                break
        return self

    def to_bytes(self, compress=True):
        out = [MAGIC, struct.pack("<Hii", self.version, self.num_classes, self.num_instances), self.reserved]
        for ch in self.chunks:
            name = ch.name.encode("ascii").ljust(4, b"\0")[:4]
            data = ch.data
            if compress and ch.name != "END" and _lz4 is not None and len(data) > 0:
                comp = _lz4.compress(data, store_size=False)
                out.append(name + struct.pack("<III", len(comp), len(data), 0))
                out.append(comp)
            else:
                out.append(name + struct.pack("<III", 0, len(data), 0))
                out.append(data)
        return b"".join(out)

    def save(self, path, compress=True):
        with open(path, "wb") as f:
            f.write(self.to_bytes(compress))

    # ------------------------------------------------------------ helpers
    def class_names(self):
        """class id -> (class name, instance count)"""
        res = {}
        for ch in self.chunks:
            if ch.name == "INST":
                cid, = struct.unpack_from("<I", ch.data, 0)
                n, = struct.unpack_from("<I", ch.data, 4)
                name = ch.data[8:8 + n].decode("utf-8", "replace")
                count, = struct.unpack_from("<I", ch.data, 8 + n + 1)
                res[cid] = (name, count)
        return res

    def string_props(self):
        """Yield PropChunk views for string-typed (String / ProtectedString) PROP chunks."""
        classes = self.class_names()
        for ch in self.chunks:
            if ch.name != "PROP":
                continue
            pc = PropChunk(ch)
            if pc.type in (PT_STRING, PT_PROTECTED_STRING):
                pc.class_name, pc.count = classes.get(pc.class_id, ("?", 0))
                yield pc


class PropChunk:
    """View over a PROP chunk; supports decoding/re-encoding string values."""

    def __init__(self, chunk):
        self.chunk = chunk
        d = chunk.data
        self.class_id, n = struct.unpack_from("<II", d, 0)
        self.name = d[8:8 + n].decode("utf-8", "replace")
        self.type = d[8 + n]
        self._values_off = 9 + n
        self.class_name = "?"
        self.count = 0

    def values(self):
        d = self.chunk.data
        o = self._values_off
        res = []
        for _ in range(self.count):
            ln, = struct.unpack_from("<I", d, o)
            res.append(d[o + 4:o + 4 + ln])
            o += 4 + ln
        return res

    def set_values(self, values, prop_type=None):
        if prop_type is None:
            prop_type = self.type
        name = self.name.encode("utf-8")
        parts = [struct.pack("<II", self.class_id, len(name)), name, bytes([prop_type])]
        for v in values:
            parts.append(struct.pack("<I", len(v)))
            parts.append(v)
        self.chunk.data = b"".join(parts)
        self.type = prop_type
        self._values_off = 9 + len(name)
