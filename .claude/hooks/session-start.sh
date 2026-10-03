#!/bin/bash
# Installs the pinned Bend version at the start of each Claude Code cloud
# session (the container is wiped between sessions). See docs/bend-notes.md.
#
# Bend is pinned: we download the release archive straight from GitHub and
# check it against a known sha256, rather than running bend-lang.com's
# install.sh, which always installs the latest version. To upgrade Bend, change
# BEND_VERSION and BEND_SHA256 together, on purpose, and note it in
# docs/bend-notes.md.
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

BEND_VERSION="2.0.35"
BEND_SHA256="63039d1a119f716767ac5a7d8fe0717cfacf219c6c253c35192148e0dade722f" # linux-x64
BEND_HOME="$HOME/.bend"
BEND="$BEND_HOME/bin/bend"

installed_version() {
  "$BEND" version 2>/dev/null | awk '{print $2}' || true
}

found=$(installed_version)
if [ "$found" != "$BEND_VERSION" ]; then
  if [ -n "$found" ]; then
    echo "WARNING: found Bend $found, replacing it with the pinned $BEND_VERSION." >&2
  fi
  name="bend-$BEND_VERSION-linux-x64.tar.gz"
  url="https://github.com/bendlang/bend/releases/download/v$BEND_VERSION/$name"
  tmp=$(mktemp -d)
  trap 'rm -rf "$tmp"' EXIT
  echo "Installing Bend $BEND_VERSION from $url"
  curl --proto '=https' --tlsv1.2 -fsSL -o "$tmp/$name" "$url"
  echo "$BEND_SHA256  $tmp/$name" | sha256sum -c - >/dev/null
  # --warning=no-unknown-keyword hides the harmless macOS xattr warnings
  tar --warning=no-unknown-keyword -xzf "$tmp/$name" -C "$tmp"
  mkdir -p "$BEND_HOME/bin"
  rm -rf "$BEND_HOME/bend2" "$BEND_HOME/guide"
  mv "$tmp/bend/bend2" "$tmp/bend/guide" "$BEND_HOME/"
  mv -f "$tmp/bend/bin/bend" "$BEND"
fi

if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo "export PATH=\"$BEND_HOME/bin:\$PATH\"" >> "$CLAUDE_ENV_FILE"
  echo "export BEND_NO_TELEMETRY=1" >> "$CLAUDE_ENV_FILE"
fi

got=$(installed_version)
if [ "$got" != "$BEND_VERSION" ]; then
  echo "WARNING: expected Bend $BEND_VERSION but found '${got:-nothing}'." \
    "Results may differ from earlier milestones; check docs/bend-notes.md." >&2
else
  echo "Bend $got ready."
fi
