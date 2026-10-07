module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.IntClosed
public import ReasLib.CategoryTheory.Monoidal.Bimod.InternalHom
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.8.2

The reusable statement is made at the level of bimodule objects in a monoidal category equipped
with a chosen right internal Hom, equalizers, and balanced tensor products. Integer-graded module
sheaves on a ringed site obtain this datum canonically from the imported closed braided structure.
-/

open CategoryTheory

/- Lemma 24.8.2 (0FR6), part (1): for a right `A`-module `M`, an `(A, B)`-bimodule
`N`, and a right `B`-module `L`, maps `M ⊗_A N ⟶ L` are naturally equivalent to maps
`M ⟶ Hom_B(N, L)`. -/
@[stacks 0FR6] #check @Bimod.InternalHom.homEquiv

/- The Hom-set equivalence is owned by an adjunction of reusable functors. -/
#check @Bimod.InternalHom.adjunction

/- Its variance in `M`, `N`, and `L` is exposed separately for rewriting. -/
#check @Bimod.InternalHom.homEquiv_natural_source
#check @Bimod.InternalHom.homEquiv_natural_bimodule
#check @Bimod.InternalHom.homEquiv_natural_target

/- Lemma 24.8.2 (0FR6), part (2): relative internal Hom out of `M ⊗_A N` is
naturally isomorphic to the iterated relative internal Hom `Hom_A(M, Hom_B(N, -))`. -/
@[stacks 0FR6 "internal Hom currying"] #check @Bimod.InternalHom.tensorNatIso

/- The source's three-object formulation is the component of this natural isomorphism. -/
#check @Bimod.InternalHom.tensorIso

/- Naturality of internal-Hom currying in all three source variables. -/
#check @Bimod.InternalHom.tensorIso_natural_source
#check @Bimod.InternalHom.tensorIso_natural_bimodule
#check @Bimod.InternalHom.tensorIso_natural_target

/- The actual integer-graded ringed-site application uses a globally inferable closed structure,
so no chapter-local instance or auxiliary `let` is needed. -/
#check @SheafOfModules.RingedSite.IntGraded.monoidalClosed
#check @CategoryTheory.RightInternalHom.ofBraidedClosed
