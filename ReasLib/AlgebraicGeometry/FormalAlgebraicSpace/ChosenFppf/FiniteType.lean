module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.LocalMorphismProperty
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.FiniteType
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType

/-!
# Local finite type on the chosen fppf site

Local finite type of morphisms of locally countably indexed formal algebraic
spaces is characterized by taut, topologically finite-type affine étale charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

universe u v

namespace AlgebraicGeometry.IsLocallyCountablyIndexed

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
variable [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
variable [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]

/-- A morphism of sheaves on `(Sch/S)_fppf` is locally of finite type when it
is representable by algebraic spaces and every scheme pullback is locally of
finite type as a morphism of algebraic spaces. -/
@[mk_iff]
class LocallyOfFiniteType {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) : Prop where
  /-- The morphism is representable by algebraic spaces. -/
  representable : representableByAlgebraicSpaces f
  /-- Every scheme pullback is locally of finite type in the algebraic-space sense. -/
  of_pullback :
    ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
      locallyOfFiniteTypeOnEtaleSquares (pullback.fst ξ f)

namespace LocallyOfFiniteType

/-- The identity morphism of a sheaf on `(Sch/S)_fppf` is locally of finite type. -/
instance id {X : Sheaf (𝒮.bigTopology S) (Type (max u v))} :
    LocallyOfFiniteType (𝟙 X) := sorry

/-- A locally finite-type morphism is representable by algebraic spaces and
every scheme pullback is locally of finite type as a morphism of algebraic spaces. -/
theorem spec {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))} (f : X ⟶ Y)
    [LocallyOfFiniteType f] :
    representableByAlgebraicSpaces f ∧
      ∀ ⦃U : 𝒮.bigSite S⦄ (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
        locallyOfFiniteTypeOnEtaleSquares (pullback.fst ξ f) :=
  ⟨LocallyOfFiniteType.representable, LocallyOfFiniteType.of_pullback⟩

end LocallyOfFiniteType

variable {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}

/-- For a morphism of locally countably indexed formal algebraic spaces,
local finite type is equivalent to taut topological finite type on every
affine étale square, on a target cover and covers of its pullbacks, or on a
source cover factoring through affine étale target charts. -/
theorem locallyOfFiniteType_tfae
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    List.TFAE
      [etaleAffineLocally (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnTarget (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
        existsCoverOnSource (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f,
        LocallyOfFiniteType f] := sorry

/-- Local finite type is equivalent to taut topological finite type on every
affine étale-chart square. -/
theorem etaleAffineLocally_iff_locallyOfFiniteType
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    etaleAffineLocally (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f ↔
      LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 0 3

/-- Local finite type is equivalent to admitting an affine étale target cover
and affine étale covers of its pullbacks whose maps to the target charts
correspond to taut topologically finite-type ring homomorphisms. -/
theorem existsCoverOnTarget_iff_locallyOfFiniteType
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnTarget (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f ↔
      LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 1 3

/-- Local finite type is equivalent to admitting an affine étale source cover
factoring through affine étale target charts by morphisms corresponding to
taut topologically finite-type ring homomorphisms. -/
theorem existsCoverOnSource_iff_locallyOfFiniteType
    [IsLocallyCountablyIndexed X] [IsLocallyCountablyIndexed Y]
    (f : X ⟶ Y) [Fact (ChosenBigSite.IsSizeClosed 𝒮)] :
    existsCoverOnSource (fun φ => φ.IsTaut ∧ φ.TopologicallyOfFiniteType) f ↔
      LocallyOfFiniteType f :=
  (locallyOfFiniteType_tfae f).out 2 3

end AlgebraicGeometry.IsLocallyCountablyIndexed
