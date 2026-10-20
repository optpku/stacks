module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Dualizing.EtaleLocal

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- An object of `D_QCoh(𝒪_X)` on a locally Noetherian algebraic space over `S` is a
dualizing complex when its restriction to every étale scheme chart is dualizing. -/
def IsDualizingComplex {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) : Prop :=
  forallEtaleScheme K

/-- `IsDualizingComplex K` is equivalent to dualizingness of the restriction of `K`
along every étale scheme chart. -/
theorem isDualizingComplex_iff {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    IsDualizingComplex K ↔ forallEtaleScheme K :=
  sorry

/-- `IsDualizingComplex K` is equivalent to the existence of a surjective étale scheme
chart along which the restriction of `K` is dualizing. -/
theorem isDualizingComplex_iff_existsSurjectiveEtaleScheme {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsLocallyNoetherian X] (K : DerivedQCoh X) :
    IsDualizingComplex K ↔ existsSurjectiveEtaleScheme K :=
  sorry

namespace IsDualizingComplex

/-- Dualizingness of the restriction of `K` along every étale scheme chart witnesses that
`K` is a dualizing complex. -/
theorem of_forall {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : forallEtaleScheme K) : IsDualizingComplex K :=
  sorry

/-- A surjective étale scheme chart along which the restriction of `K` is dualizing
witnesses that `K` is a dualizing complex. -/
theorem of_exists {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : existsSurjectiveEtaleScheme K) :
    IsDualizingComplex K :=
  sorry

/-- A dualizing complex satisfies both equivalent étale-scheme-chart conditions. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : IsDualizingComplex K) :
    forallEtaleScheme K ∧ existsSurjectiveEtaleScheme K :=
  sorry

/-- Restriction of a dualizing complex along an étale scheme chart is dualizing. -/
theorem restrict {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    {K : DerivedQCoh X} (h : IsDualizingComplex K) {U : Over S}
    (φ : ofOver U ⟶ X) [Etale φ]
    [AlgebraicGeometry.IsLocallyNoetherian U.left] :
    isDualizingOnScheme U
      ((ModuleDerived.pullback φ).obj ((inclusion X).obj K)) :=
  sorry

end IsDualizingComplex

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
