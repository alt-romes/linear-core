The first attempt of an implementation tried converting from Core to Linear Core
first, and then typecheck linear core separately.
Apart from a bit contrived and likely more complicated (how to remove type
applications, coercions, pattern synonyms, AppTy, etc...), the system changed
considerably towards the end, so we reimplemented it from scratch:

Currently, the only modules that are not outdated with dropped implementations are
`Linear.Core`, `Linear.Core.Monad`, and the first part of `Linear.Core.Plugin`.

Later on we can move them out of the package into an "outdated things" one, but
for now it doesn't matter.
