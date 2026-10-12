/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap87.Lemma_87_16_2_Pullback

/-!
# Separated algebraic spaces on a chosen big fppf site

A sheaf on `(Sch/S)_fppf` is a separated algebraic space when it is an
algebraic space and fibre products of morphisms from affine schemes into it
are affine with surjective `ℤ`-tensor map on global sections.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry.ChosenBigFppfSite

/-- A sheaf on `(Sch/S)_fppf` is a separated algebraic space when it is an
algebraic space and fibre products of morphisms from affine schemes to it
are affine with surjective `Γ(U, ⊤) ⊗[ℤ] Γ(V, ⊤) ⟶ Γ(U ×_X V, ⊤)`. -/
class IsSeparated {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsAlgebraicSpace X where
  /-- Fibre products of morphisms from affine schemes to `X` are affine with
  surjective `sectionTensor`. -/
  affine_pullback_surjective : forallAffinePullbackAffineSurjective X

namespace IsSeparated

/-- The sheafified representable of an affine object of `(Sch/S)_fppf` is a
separated algebraic space. -/
instance instSheafifiedRepresentable {𝒮 : ChosenBigFppfSite.{u, v}}
    {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (U : 𝒮.bigAffineSite S) :
    IsSeparated ((𝒮.bigTopology S).sheafifiedRepresentable
      ((𝒮.bigAffineInclusion S).obj U)) where
  affine_pullback_surjective := sorry

/-- A sheaf is a separated algebraic space iff it is an algebraic space and
fibre products of morphisms from affine schemes to it are affine with
surjective `sectionTensor`. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsSeparated X ↔
      IsAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X :=
  sorry

/-- A separated algebraic space unpacks as an algebraic space together with
affine fibre products of morphisms from affine schemes and surjective
`sectionTensor`. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) [IsSeparated X] :
    IsAlgebraicSpace X ∧ forallAffinePullbackAffineSurjective X :=
  sorry

/-- Affine fibre products of morphisms from affine schemes with surjective
`sectionTensor` witness that an algebraic space sheaf is separated. -/
theorem of {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} [IsAlgebraicSpace X]
    (h : forallAffinePullbackAffineSurjective X) : IsSeparated X :=
  sorry

end IsSeparated

end AlgebraicGeometry.ChosenBigFppfSite
