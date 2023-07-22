{-
On using usage environments instead of unrestricted and linear resources (empty UE vs exactly one UE vs complex UE):
* This isn't useful for linear resources, since they would have to appear once in the linear context and another in the delta environment, we'd have double the bookkeeping there
* However, for unrestricted resources, this seems like a great idea:
  * It would uniformise/get rid completely of the distinction between unrestricted and empty-usage-environment variables
  * And means we could get rid of the unrestricted environment completely!
  * However, the delta context doesn't have Contract. Should be simple to fix a way for empty-usage-env/unrestricted variables (talvez uma regra explícita de contract para quando os environments estão vazios, porque fzemos o split na mesma)
  * Se bem que neste momento estou a por type variables e constructors no Unrestricted. Mas os Constructors parecem-me tmb bem no Delta. As type variables é que já não sei. Se calhar a distinção dá jeito, tendo em conta que no Core há mais coisas unrestricted (coercions, ...)
-}
