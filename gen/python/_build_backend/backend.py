"""Build Python messages from the repository schema; ship them in distributions."""

import json
import shutil
import subprocess
from pathlib import Path
from tempfile import TemporaryDirectory

from setuptools import build_meta as _setuptools

_PACKAGE = Path(__file__).resolve().parents[1]
_REPOSITORY = _PACKAGE.parents[1]


def get_requires_for_build_wheel(config_settings=None):
    # Sdists already contain generated messages and need no codegen tools.
    return (
        ["protoc-gen-py==0.5.0"]
        if not (_PACKAGE / "PKG-INFO").is_file()
        and (_REPOSITORY / "proto/egglog/v1/egglog.proto").is_file()
        else []
    )


get_requires_for_build_sdist = get_requires_for_build_wheel
get_requires_for_build_editable = get_requires_for_build_wheel


def _prepare():
    distribution = (_PACKAGE / "PKG-INFO").is_file()
    if not distribution and (_REPOSITORY / "proto/egglog/v1/egglog.proto").is_file():
        # A source checkout must regenerate successfully, even if old output exists.
        # Only the Python plugin is needed; Buf resolves imports through buf.lock.
        with TemporaryDirectory() as temporary:
            template = {
                "version": "v2",
                "inputs": [{"directory": "proto"}],
                "plugins": [
                    {
                        "local": "protoc-gen-py",
                        "out": temporary,
                        "include_imports": True,
                    }
                ],
            }
            subprocess.run(
                ["buf", "generate", "--template", json.dumps(template)],
                cwd=_REPOSITORY,
                check=True,
            )
            for name in ("egglog", "buf"):
                shutil.rmtree(_PACKAGE / name, ignore_errors=True)
                shutil.copytree(Path(temporary) / name, _PACKAGE / name)
    elif not distribution:
        raise RuntimeError(
            "Build from the full Git checkout or a generated source distribution"
        )
    for name in ("egglog/v1/egglog_pb.py", "buf/validate/validate_pb.py"):
        if not (_PACKAGE / name).is_file():
            raise RuntimeError(f"Generated source distribution is missing {name}")


def build_wheel(wheel_directory, config_settings=None, metadata_directory=None):
    _prepare()
    return _setuptools.build_wheel(wheel_directory, config_settings, metadata_directory)


def build_sdist(sdist_directory, config_settings=None):
    _prepare()
    return _setuptools.build_sdist(sdist_directory, config_settings)


def build_editable(wheel_directory, config_settings=None, metadata_directory=None):
    _prepare()
    return _setuptools.build_editable(
        wheel_directory, config_settings, metadata_directory
    )
