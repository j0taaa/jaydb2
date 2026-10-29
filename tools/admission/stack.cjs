const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const hash = data => crypto.createHash('sha256').update(data).digest('hex');
const pin = JSON.parse(fs.readFileSync(path.join(__dirname, 'frontend.lock.json')));
if (pin.node !== process.version || pin.nodeModuleVersion !== process.versions.modules)
  throw new Error('Frontend native stack addon requires its pinned Node runtime');
if (hash(fs.readFileSync(path.join(__dirname, 'stack.cc'))) !== pin.stackSourceSha256)
  throw new Error('Frontend stack source pin mismatch');
const binary = path.join(__dirname, 'installed', 'stack.node');
if (hash(fs.readFileSync(binary)) !== pin.files['stack.node'])
  throw new Error('Frontend stack binary pin mismatch');
require(binary);
