import assert from "node:assert/strict";

export async function packageStatus(archive, {
  request = globalThis.fetch,
  timeoutMs = 15_000,
} = {}) {
  let response;
  let metadata;
  try {
    // Full packuments avoid cached 404s from exact-version URLs.
    response = await request(`https://registry.npmjs.org/${encodeURIComponent(archive.name)}`, {
      headers: { accept: "application/json", "cache-control": "no-cache", pragma: "no-cache" },
      cache: "no-store",
      signal: AbortSignal.timeout(Math.max(1, timeoutMs)),
    });
    if (response.ok) metadata = await response.json();
  } catch (error) {
    return { ready: false, reason: error.message };
  }
  if (!response.ok) {
    assert(response.status === 404 || response.status === 408 || response.status === 429 || response.status >= 500,
      `Public npm registry returned HTTP ${response.status} for ${archive.name}`);
    return { ready: false, missing: response.status === 404, reason: `HTTP ${response.status}` };
  }
  const version = metadata?.versions?.[archive.metadata.version];
  if (!version) return { ready: false, missing: true, reason: `version ${archive.metadata.version} is not visible` };
  assert.equal(version.dist?.integrity, archive.integrity,
    `Public npm integrity mismatch for ${archive.name}@${archive.metadata.version}`);
  return { ready: true };
}

export async function waitForNativePackages(packages, {
  timeoutMs = 10 * 60_000,
  intervalMs = 10_000,
  request = globalThis.fetch,
  now = Date.now,
  sleep = (milliseconds) => new Promise((resolve) => setTimeout(resolve, milliseconds)),
  log = console.log,
} = {}) {
  const started = now();
  const deadline = started + timeoutMs;
  const pending = new Map(packages.map((archive) => [archive.name, archive]));
  const reasons = new Map();
  let previousCount;
  let lastProgress = started;
  while (pending.size && now() < deadline) {
    await Promise.all([...pending.values()].map(async (archive) => {
      const remaining = deadline - now();
      if (remaining <= 0) return;
      const status = await packageStatus(archive, { request, timeoutMs: Math.min(15_000, remaining) });
      if (status.ready) {
        pending.delete(archive.name);
        reasons.delete(archive.name);
      } else {
        reasons.set(archive.name, status.reason);
      }
    }));
    if (!pending.size) break;
    if (pending.size !== previousCount || now() - lastProgress >= 60_000) {
      log(`Waiting for ${pending.size} native npm package(s) to become public (${Math.floor((now() - started) / 1000)}s elapsed): ${[...pending.keys()].join(", ")}`);
      previousCount = pending.size;
      lastProgress = now();
    }
    const remaining = deadline - now();
    if (remaining > 0) await sleep(Math.min(intervalMs, remaining));
  }
  if (pending.size) {
    log(`Registry processing is still pending: ${[...pending.keys()].map((name) => `${name} (${reasons.get(name) ?? "not checked"})`).join(", ")}`);
    return false;
  }
  log(`All ${packages.length} native npm package versions are public with matching integrity.`);
  return true;
}
