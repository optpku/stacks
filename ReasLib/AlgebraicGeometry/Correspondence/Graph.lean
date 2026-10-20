module

public import ReasLib.AlgebraicGeometry.BivariantClass.ProperPushforward
public import ReasLib.AlgebraicGeometry.BivariantClass.Rationalization
public import ReasLib.AlgebraicGeometry.ChowCohomology
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Graph
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Product
public import ReasLib.RingTheory.Catenary.Field
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.Affine

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Correspondence

variable {k : Type u} [Field k]

/-- The graph map `(f, 𝟙 Y) : Y ⟶ X ⨯ Y` is proper when `X` is separated over the field. -/
instance graphMap_isProper
    {X Y : SchemeOverField k} [IsSeparated X.hom] (f : Y ⟶ X) :
    IsProper (Limits.prod.lift f (𝟙 Y)).left := sorry

/-- The integral degree-zero graph correspondence obtained by proper pushforward of the
identity bivariant class along `(f, 𝟙 Y) : Y ⟶ X ⨯ Y`. -/
noncomputable def integralGraph
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    BivariantClass (fun _ ↦ 0) (Limits.prod.snd : X ⨯ Y ⟶ Y) 0 :=
  BivariantClass.properPushforward (fun _ ↦ 0) (Limits.prod.lift f (𝟙 Y))
    Limits.prod.snd 0
    (let hcomp : Limits.prod.lift f (𝟙 Y) ≫ Limits.prod.snd = (𝟙 Y : Y ⟶ Y) :=
      Limits.prod.lift_snd f (𝟙 Y)
    hcomp.symm ▸
      ChowCohomology.one (fun _ ↦ 0) Y.hom)

/-- The integral graph correspondence is proper pushforward of the identity bivariant class. -/
theorem integralGraph_def
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    integralGraph f =
      BivariantClass.properPushforward (fun _ ↦ 0) (Limits.prod.lift f (𝟙 Y))
        Limits.prod.snd 0
        (let hcomp : Limits.prod.lift f (𝟙 Y) ≫ Limits.prod.snd = (𝟙 Y : Y ⟶ Y) :=
          Limits.prod.lift_snd f (𝟙 Y)
        hcomp.symm ▸
          ChowCohomology.one (fun _ ↦ 0) Y.hom) := sorry

/-- The rational degree-zero graph correspondence obtained by scalar extension from `ℤ` to
`ℚ`. -/
noncomputable def rationalGraph
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    BivariantClass.RationalBivariantClass (fun _ ↦ 0)
      (Limits.prod.snd : X ⨯ Y ⟶ Y) 0 :=
  BivariantClass.rationalize (fun _ ↦ 0)
    (Limits.prod.snd : X ⨯ Y ⟶ Y) 0 (integralGraph f)

/-- The rational graph correspondence is the tensor rationalization of its integral class. -/
theorem rationalGraph_def
    {X Y : SchemeOverField k} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [IsSeparated X.hom] (f : Y ⟶ X) :
    rationalGraph f =
      BivariantClass.rationalize (fun _ ↦ 0)
        (Limits.prod.snd : X ⨯ Y ⟶ Y) 0 (integralGraph f) := sorry

end AlgebraicGeometry.Correspondence
