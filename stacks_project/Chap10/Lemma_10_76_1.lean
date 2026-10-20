module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.76.1

Flat base change for `Tor` is owned by the reusable comparison in
`CategoryTheory.ModuleCat.Tor.Flat`, rather than by this chapter entry.

@stack 00M8
-/

/- Lemma 10.76.1 [stacks 00M8]: for a flat ring map `R →+* S`, the canonical
map from scalar extension of `Tor_n^R(M, N)` to
`Tor_n^S(M ⊗[R] S, N ⊗[R] S)` is an isomorphism.  The shared owner exposes the
underlying morphism, its structured isomorphism, and the `IsIso` fact separately. -/
@[stacks 00M8]
#check @CategoryTheory.ModuleCat.Tor.Flat.baseChange

#check @CategoryTheory.ModuleCat.Tor.Flat.baseChangeIso
#check @CategoryTheory.ModuleCat.Tor.Flat.baseChange_isIso
