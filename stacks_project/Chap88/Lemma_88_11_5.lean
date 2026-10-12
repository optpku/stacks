/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star
public import stacks_project.Chap87.Lemma_87_29_9
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType

/-!
# Finite type morphisms of locally adic* formal algebraic spaces

Lemma 88.11.5 records that a morphism of locally adic* formal algebraic
spaces is locally of finite type if and only if its étale affine charts, or
some Definition 87.11.1 covering of the target or of the source, correspond
to adic topologically finite-type maps of `WAdm^{adic*}`.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing RingHom
open AlgebraicGeometry.IsLocallyCountablyIndexed (LocallyOfFiniteType)

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]

/-- Lemma 88.11.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
locally adic* formal algebraic spaces over `S`. The following are equivalent:
`etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f`,
that every commutative square of affine formal algebraic spaces over `f` with
representable étale vertical arrows has top arrow corresponding to an adic
topologically finite-type map `B →+* A` of `WAdm^{adic*}`;
`existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f`,
that some covering `{Y_ j ⟶ Y}` as in Definition 87.11.1 has, for each `j`, a
covering `{X_ ji ⟶ Y_ j ×_Y X}` as in Definition 87.11.1 whose maps
`X_ ji ⟶ Y_ j` correspond to adic topologically finite-type maps of
`WAdm^{adic*}`;
`existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f`,
that some covering `{X_ i ⟶ X}` as in Definition 87.11.1 factors as
`X_ i ⟶ Y_ i ⟶ Y` with each `Y_ i` an affine formal algebraic space, each
`Y_ i ⟶ Y` representable by algebraic spaces and étale, and each
`X_ i ⟶ Y_ i` corresponding to an adic topologically finite-type map of
`WAdm^{adic*}`; and `IsLocallyCountablyIndexed.LocallyOfFiniteType f`. -/
@[stacks 0GC0]
theorem locallyOfFiniteType_tfae (f : X ⟶ Y) :
    List.TFAE
      [etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        IsLocallyCountablyIndexed.LocallyOfFiniteType f] :=
  sorry

/-- Condition (1) of Lemma 88.11.5 is equivalent to condition (4): testing adic
topologically finite-type charts on every étale affine-chart square is
equivalent to `f` being locally of finite type. -/
theorem etaleAffineLocally_iff_locallyOfFiniteType (f : X ⟶ Y) :
    etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  sorry

/-- Condition (2) of Lemma 88.11.5 is equivalent to condition (4): a
Definition 87.11.1 covering of the target and then of each fibre product
witnesses adic topologically finite-type charts iff `f` is locally of finite
type. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteType (f : X ⟶ Y) :
    existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  sorry

/-- Condition (3) of Lemma 88.11.5 is equivalent to condition (4): a
Definition 87.11.1 covering of the source factoring through affine étale
charts of the target witnesses adic topologically finite-type charts iff `f`
is locally of finite type. -/
theorem existsCoverOnSource_iff_locallyOfFiniteType (f : X ⟶ Y) :
    existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f :=
  sorry

end AlgebraicGeometry.IsLocallyAdicStar
