module

public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.PresentationRestriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.VanishingH1
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.HigherDirectImage

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.QCoh

/-- An injective quasi-coherent module on a Noetherian algebraic space has vanishing
positive-degree cohomology after restriction to every quasi-compact and quasi-separated
algebraic space étale over it. -/
@[stacks 09TL]
theorem cohomology_restrict_isZero_of_injective
    {S : Scheme.{u}} {X U : AlgebraicSpace S} [IsNoetherian X]
    (j : U ⟶ X) [Etale j] [IsQuasiCompact U] [IsAbsolutelyQuasiSeparated U]
    (J : QCoh X) [Injective J] {p : ℕ} (hp : 0 < p)
    [HasSheafify (smallEtaleTopology U) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (smallEtaleTopology U) AddCommGrpCat.{u})] :
    IsZero (cohomology U (Modules.restrict ((inclusion X).obj J) j) p) :=
  sorry

section

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `higherDirectImage`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/-- An injective quasi-coherent module on a Noetherian algebraic space has vanishing
positive higher direct images along every morphism to a quasi-separated algebraic space. -/
@[stacks 09TL]
theorem higherDirectImage_isZero_of_injective
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsNoetherian X] [IsAbsolutelyQuasiSeparated Y]
    (f : X ⟶ Y) (J : QCoh X) [Injective J]
    [Abelian X.Modules] [Abelian Y.Modules] [HasInjectiveResolutions X.Modules]
    {p : ℕ} (hp : 0 < p) :
    IsZero (Modules.higherDirectImage f ((inclusion X).obj J) p) :=
  sorry

end

end AlgebraicGeometry.AlgebraicSpace.QCoh
