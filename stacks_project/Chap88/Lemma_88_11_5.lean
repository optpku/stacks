module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.AdicStarFiniteType
import StacksCheckRecall

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

namespace AlgebraicGeometry.IsLocallyAdicStar

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
variable [IsLocallyAdicStar X] [IsLocallyAdicStar Y]

/- Lemma 88.11.5: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
#check (AlgebraicGeometry.IsLocallyAdicStar.locallyOfFiniteType_tfae :
  ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    List.TFAE
      [etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f,
        IsLocallyCountablyIndexed.LocallyOfFiniteType f])

#check (AlgebraicGeometry.IsLocallyAdicStar.etaleAffineLocally_iff_locallyOfFiniteType :
  ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    etaleAffineLocally (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f)

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnTarget_iff_locallyOfFiniteType :
  ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    existsCoverOnTarget (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f)

#check (AlgebraicGeometry.IsLocallyAdicStar.existsCoverOnSource_iff_locallyOfFiniteType :
  ∀ (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)],
    existsCoverOnSource (fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) f ↔
      IsLocallyCountablyIndexed.LocallyOfFiniteType f)

end AlgebraicGeometry.IsLocallyAdicStar
