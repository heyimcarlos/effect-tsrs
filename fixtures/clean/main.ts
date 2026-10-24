import { Effect, Option, Exit } from "effect"
import { pipe } from "effect/Function"

const value: Effect.Effect<number> = Effect.succeed(1)
const transform = (n: number) => n + 1
export const program = pipe(value, Effect.map(transform))
export const regular = () => program
let assigned = value
assigned = Effect.succeed(2)
assigned ??= value
assigned ||= value
assigned &&= value
Option.some(1)
Exit.succeed(1)
const lookalike = { succeed: (value: number) => ({ value }) }
lookalike.succeed(1)
const lookalikePipe = <A>(value: A): A => value
lookalikePipe(1)
