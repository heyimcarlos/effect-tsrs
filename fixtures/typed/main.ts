import { Effect as E, Exit, Option, Pool } from "effect"
import * as F from "effect/Function"
import { Fx, Flow, pipeline } from "./reexports.js"

const typed: E.Effect<number> = E.succeed(1)
function make(): E.Effect<number> { return typed }
typed
make()
Fx.succeed("renamed re-export")
const stream: Flow.Stream<number> = Flow.succeed(1)
stream
// 😀 before diagnostics; the second emoji also changes same-line UTF-16 positions.
"😀"; E.succeed("unicode 😀")

let assigned: E.Effect<number> = typed
assigned = E.succeed(2)
assigned ??= typed
assigned ||= typed
assigned &&= typed
const kept = make()
const transformed = typed.pipe(E.map((n) => n + 1))
const transformedFunction = F.pipe(typed, E.map((n) => n + 1))
const noArguments = typed.pipe()
const noTransform = F.pipe(typed)
const renamedPipe = pipeline(typed)
const alias = pipeline
const aliasPipe = alias(typed)

Exit.succeed(1)
Option.some(1)
export const pool = Pool.make({ acquire: typed, size: 1 })

export async function namedAsync() { return 1 }
export const arrowAsync = async () => 2
export const expressionAsync = async function() { return 3 }
export const methods = { async method() { return 4 } }
// 😀 Unicode before the location of an async arrow on the same line.
"😀"; export const unicodeAsync = async () => "😀"

namespace Lookalike {
  export interface Effect<A> { readonly value: A }
  export const Effect = { succeed: <A>(value: A): Effect<A> => ({ value }) }
  export const pipe = <A>(value: A): A => value
}
Lookalike.Effect.succeed(1)
Lookalike.pipe(1)
const fakePipeable = { pipe: () => 1 }
// Upstream intentionally recognizes this structural .pipe() form.
fakePipeable.pipe()
const pipe = <A>(value: A): A => value
pipe(1)
