#!/usr/bin/env python3
"""Fetch and run the pinned official Bend distribution without global installation."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
LOCK = json.loads((ROOT / "tools/admission/toolchain.lock.json").read_text())
VERSION = LOCK["version"]
ARCHIVES = {
    ("Linux", "x86_64"): (
        "linux-x64", "6cf462fd8f70b094a4950ebb709a9c4ffd8f1d1189d9cedf1fd63cd5d041c7ab"
    ),
    ("Linux", "aarch64"): (
        "linux-arm64", "71b43e1bb9313dd14ac2b0553b854e41c39d65ecaa47040796ebff4a46f54a97"
    ),
    ("Darwin", "arm64"): (
        "darwin-arm64", "d4aaef68de545727429ce83b9e88ff3273bf068df599e3542e446755b5f3d83a"
    ),
    ("Darwin", "x86_64"): (
        "darwin-x64", "a512cfd1d29ec24c640126a6a640e597b4ea1abe0aefbda7cc57efd85ab56e22"
    ),
}


def environment() -> dict[str, str]:
    env = os.environ.copy()
    env["BEND_NO_TELEMETRY"] = "1"
    kernel = ROOT / ".tools" / ("bendtt-" + LOCK["kernelSha256"])
    if kernel.is_file():
        if hashlib.sha256(kernel.read_bytes()).hexdigest() != LOCK["kernelSha256"]:
            raise RuntimeError("Local official BendTT was modified")
        env["BENDTT"] = str(kernel)
    else:
        env.pop("BENDTT", None)
    return env


def verify_version(executable: Path) -> Path:
    if (platform.system(), platform.machine()) == ("Linux", "x86_64"):
        if hashlib.sha256(executable.read_bytes()).hexdigest() != LOCK["officialBinarySha256"]:
            raise RuntimeError("The executable does not match the pinned official Bend")
    version = subprocess.run(
        [str(executable), "version"], env=environment(), capture_output=True,
        text=True, check=True, timeout=15,
    )
    if version.stdout.strip() != f"bend {VERSION}":
        raise RuntimeError(f"Bend {VERSION} required: {version.stdout.strip()!r}")
    return executable


def executable() -> Path:
    override = os.environ.get("JAYDB_BEND")
    if override:
        candidate = shutil.which(override)
        if candidate is None:
            raise RuntimeError("JAYDB_BEND does not point to an executable")
        return verify_version(Path(candidate).resolve())
    installation = ROOT / ".tools" / f"bend-{VERSION}"
    candidate = installation / "bin" / "bend"
    if candidate.is_file():
        return verify_version(candidate)
    try:
        artifact, digest = ARCHIVES[(platform.system(), platform.machine())]
    except KeyError as exc:
        raise RuntimeError("No pinned Bend distribution for this platform") from exc
    installation.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="bend-download-", dir=installation.parent) as folder:
        stage = Path(folder)
        archive = stage / "bend.tar.gz"
        url = f"https://github.com/bendlang/bend/releases/download/v{VERSION}/bend-{VERSION}-{artifact}.tar.gz"
        sha = hashlib.sha256()
        with urllib.request.urlopen(url, timeout=30) as source, archive.open("wb") as destination:
            while chunk := source.read(1024 * 1024):
                sha.update(chunk)
                destination.write(chunk)
        if sha.hexdigest() != digest:
            raise RuntimeError("Bend distribution SHA-256 differs from the pinned value")
        with tarfile.open(archive) as packed:
            packed.extractall(stage / "unpacked", filter="data")
        staged = stage / "unpacked" / "bend"
        verify_version(staged / "bin" / "bend")
        # Rename publishes the complete installation after verification.
        try:
            staged.rename(installation)
        except OSError:
            if not candidate.is_file():
                raise
    return verify_version(candidate)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("arguments", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    forwarded = args.arguments
    if forwarded[:1] == ["--"]:
        forwarded = forwarded[1:]
    return subprocess.run([str(executable()), *forwarded], env=environment()).returncode


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, RuntimeError, subprocess.SubprocessError) as error:
        print(str(error), file=sys.stderr)
        raise SystemExit(1)
