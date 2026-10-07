module

public import ReasLib.Algebra.Homology.CochainComplex.KFlat.ModuleCat.Resolution
public import ReasLib.Algebra.Homology.CochainComplex.KFlat.QuasiIso
import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor invariance for K-flat module complexes

@stack 064L

This leaf specializes the generic K-flat tensor-invariance theorem to module categories, where
K-flat resolutions are always available.  Consumers therefore need no local resolution instance.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace ModuleCat.KFlat

variable {R : Type u} [CommRing R]

/-- Tensoring an arbitrary complex of `R`-modules with a quasi-isomorphism between K-flat
complexes preserves quasi-isomorphisms. -/
@[stacks 064L "module complexes"]
theorem quasiIso_tensorHom_right
    (F : CochainComplex (ModuleCat R) ℤ) {P Q : CochainComplex (ModuleCat R) ℤ}
    (hP : P.IsKFlat) (hQ : Q.IsKFlat) (f : P ⟶ Q) [QuasiIso f] :
    QuasiIso (HomologicalComplex.tensorHom (𝟙 F) f) := sorry

end ModuleCat.KFlat
