module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Perfect.Tensor
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.47.7

Perfectness under derived tensor product is owned for arbitrary bundled ringed sites in
`RingedSite.Hom.ModuleDerived`; the chapter file is only the tagged source-facing entry.
-/

/- Lemma 21.47.7 (09JB): the derived tensor product of two perfect objects of `D(𝒪_X)` is
perfect. -/
@[stacks 09JB] #check @RingedSite.Hom.ModuleDerived.IsPerfect.tensor

end
