import assert from "node:assert/strict";
import test from "node:test";
import { packageStatus, waitForNativePackages } from "./npm-registry.mjs";

const archive = { name: "@yielded/example", metadata: { version: "1.2.3" }, integrity: "sha512-matching" };
const response = (integrity = archive.integrity) => ({
  ok: true,
  json: async () => ({ versions: { "1.2.3": { dist: { integrity } } } }),
});
function clock() {
  let time = 0;
  return { now: () => time, sleep: async (duration) => { time += duration; }, log: () => {}, timeoutMs: 30, intervalMs: 10 };
}

test("delayed registry processing is pending, and a later continuation succeeds", async () => {
  const pending = { request: async () => ({ ok: true, json: async () => ({ versions: {} }) }), ...clock() };
  assert.equal(await waitForNativePackages([archive], pending), false);
  assert.equal(await waitForNativePackages([archive], { request: async () => response(), ...clock() }), true);
});

test("temporary registry failures can recover within one check", async () => {
  const replies = [() => { throw new Error("connection reset"); }, () => ({ ok: false, status: 503 }), () => response()];
  assert.equal(await waitForNativePackages([archive], { request: async () => replies.shift()(), ...clock() }), true);
});

test("a missing package stays pending rather than failing the release", async () => {
  assert.equal(await waitForNativePackages([archive], { request: async () => ({ ok: false, status: 404 }), ...clock() }), false);
});

test("integrity and authorization failures are never treated as pending", async () => {
  await assert.rejects(waitForNativePackages([archive], { request: async () => response("sha512-wrong"), ...clock() }), /integrity mismatch/);
  await assert.rejects(waitForNativePackages([archive], { request: async () => ({ ok: false, status: 403 }), ...clock() }), /HTTP 403/);
});

test("an existing launcher is accepted only with the exact published integrity", async () => {
  assert.deepEqual(await packageStatus(archive, { request: async () => response() }), { ready: true });
  await assert.rejects(packageStatus(archive, { request: async () => response("sha512-wrong") }), /integrity mismatch/);
});
