module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing

/-!
# Étale local rings as strict henselizations of henselian local rings

For a decent algebraic space, the étale local ring at a geometric point is a
strict henselization of the henselian local ring at the image point.
-/

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

@[expose] public section

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

/-- Unique factorization of a geometric point through the residue-field monomorphism
`residueHom` of an elementary étale neighbourhood of its image point. -/
noncomputable def GeometricPoint.factorThroughResidueHom {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    FieldValuedPoint.Factorization xbar.toFieldValuedPoint
      (EtaleNeighborhood.residuePoint U.obj) :=
  Classical.choice
    (FieldValuedPoint.unique_factorization_of_mono
        (EtaleNeighborhood.Elementary.spec U).2.2
        ((GeometricPoint.image_eq xbar).symm.trans
          (EtaleNeighborhood.residuePoint_mk U.obj).symm)).1

/-- The factorization triangle through `residueHom` commutes with `xbar.hom`. -/
theorem GeometricPoint.factorThroughResidueHom_fac {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    ofOverHomMk (GeometricPoint.factorThroughResidueHom xbar U).schemeHom
          (GeometricPoint.factorThroughResidueHom xbar U).fac_structure ≫
        EtaleNeighborhood.residueHom U.obj =
      xbar.hom :=
  sorry

/-- Canonical lift of a geometric point through an elementary étale neighbourhood of its
image, obtained by composing the unique residue-field factorization with
`Spec(κ(u)) ⟶ U`. The image of the closed point is the selected point `U.obj.point`. -/
noncomputable def GeometricPoint.overLiftOfElementary {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    GeometricPoint.OverLift xbar U.obj.toSite :=
  GeometricPoint.OverLift.of
    (Over.homMk
      ((GeometricPoint.factorThroughResidueHom xbar U).schemeHom ≫
        (Scheme.FieldValuedPoint.residuePoint U.obj.point).hom)
      sorry)
    sorry

/-- `overLiftOfElementary` makes the triangle with `xbar.hom` commute, and its image
point on the underlying scheme is the selected elementary point. -/
theorem GeometricPoint.overLiftOfElementary_spec {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    ofOverMap (GeometricPoint.overLiftOfElementary xbar U).hom ≫ U.obj.hom = xbar.hom ∧
      (GeometricPoint.overLiftOfElementary xbar U).hom.left
          (IsLocalRing.closedPoint xbar.K) =
        U.obj.point :=
  sorry

/-- `overLiftOfElementary` is functorial in morphisms of elementary étale
neighbourhoods of the image point. -/
theorem GeometricPoint.overLiftOfElementary_map {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    {U V : EtaleNeighborhood.Elementary X xbar.image} (f : U ⟶ V) :
    GeometricPoint.OverLift.map (EtaleNeighborhood.Elementary.Hom.toSiteHom f)
        (GeometricPoint.overLiftOfElementary xbar U) =
      GeometricPoint.overLiftOfElementary xbar V :=
  sorry

/-- An elementary étale neighbourhood of the image of a geometric point admits a lift of
that geometric point through the underlying étale scheme. -/
theorem GeometricPoint.OverLift.nonempty_of_elementary {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    Nonempty (GeometricPoint.OverLift xbar U.obj.toSite) :=
  sorry

/-- Canonical germ of global sections of an elementary étale neighbourhood in the étale
local ring at a geometric point, along `overLiftOfElementary`. -/
noncomputable def etaleLocalRing.germ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤) →+*
      etaleLocalRing X xbar :=
  RingCat.Hom.hom
    ((eqToHom
        ((congrArg (fun Y : Scheme.{u} ↦ RingCat.of Γ(Y, ⊤))
            (EtaleNeighborhood.Elementary.toScheme_obj X xbar.image U).symm).trans
          (structureSheaf_obj U.obj.toSite).symm) :
        RingCat.of Γ((EtaleNeighborhood.Elementary.toScheme X xbar.image).obj U, ⊤) ⟶
          (structureSheaf X).obj.obj (op U.obj.toSite)) ≫
      (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber U.obj.toSite
        (GeometricPoint.overLiftOfElementary xbar U) (structureSheaf X).obj)

/-- Canonical comparison from the henselian local ring at the image of a geometric point
to the étale local ring at that geometric point, induced by germs of elementary étale
neighbourhoods. -/
noncomputable def etaleLocalRing.fromHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    henselianLocalRing X xbar.image →+* etaleLocalRing X xbar :=
  ULift.ringEquiv.toRingHom.comp
    (colimit.desc (EtaleNeighborhood.Elementary.sections X xbar.image)
        { pt :=
            (CommRingCat.universeLift.{u, u + 1}).obj
              (CommRingCat.of (etaleLocalRing X xbar))
          ι :=
            { app := fun j ↦
                (CommRingCat.universeLift.{u, u + 1}).map
                  (CommRingCat.ofHom
                    (etaleLocalRing.germ xbar (ULiftHom.objDown j).unop))
              naturality := fun _ _ _ ↦ sorry } }).hom

/-- The étale local ring is an algebra over the henselian local ring at the image
point. -/
noncomputable instance etaleLocalRing.instAlgebraHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    Algebra (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) :=
  (etaleLocalRing.fromHenselianLocalRing xbar).toAlgebra

/-- The étale local ring at a geometric point is a strict henselization of the
henselian local ring at the image point. -/
instance etaleLocalRing.instIsStrictHenselizationOf {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    IsStrictHenselizationOf (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) :=
  sorry

/-- `fromHenselianLocalRing` recovers the germ of global sections of an elementary étale
neighbourhood after composing with the colimit coprojection. -/
theorem etaleLocalRing.fromHenselianLocalRing_comp_ι {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X)
    (U : EtaleNeighborhood.Elementary X xbar.image) :
    (etaleLocalRing.fromHenselianLocalRing xbar).comp
        (henselianLocalRing.ι X xbar.image U) =
      etaleLocalRing.germ xbar U :=
  sorry

/-- The algebra map of `etaleLocalRing` over the henselian local ring is
`fromHenselianLocalRing`. -/
theorem etaleLocalRing.algebraMap_fromHenselianLocalRing {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) :
    algebraMap (henselianLocalRing X xbar.image) (etaleLocalRing X xbar) =
      etaleLocalRing.fromHenselianLocalRing xbar :=
  sorry

/-- If a geometric point `xbar` lies over `x ∈ |X|`, the henselian local ring at `x`
equals the henselian local ring at `xbar.image`. -/
theorem etaleLocalRing.henselianLocalRing_eq_of_liesOver {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) {x : Points X}
    (hx : xbar.liesOver x) :
    henselianLocalRing X x = henselianLocalRing X xbar.image :=
  sorry

/-- Algebra structure on the étale local ring over the henselian local ring at a point
`x` over which the geometric point lies, transported along `xbar.image = x`. -/
@[reducible] noncomputable def etaleLocalRing.algebraHenselianLocalRing_of_liesOver
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (xbar : GeometricPoint X) {x : Points X} (hx : xbar.liesOver x) :
    Algebra (henselianLocalRing X x) (etaleLocalRing X xbar) :=
  (hx : xbar.image = x) ▸ etaleLocalRing.instAlgebraHenselianLocalRing xbar

/-- The transported algebra is the image algebra after substituting `xbar.image = x`. -/
theorem etaleLocalRing.algebraHenselianLocalRing_of_liesOver_eq {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) {x : Points X}
    (hx : xbar.liesOver x) :
    etaleLocalRing.algebraHenselianLocalRing_of_liesOver xbar hx =
      ((hx : xbar.image = x) ▸ etaleLocalRing.instAlgebraHenselianLocalRing xbar) :=
  sorry

/-- If a geometric point `xbar` lies over `x ∈ |X|`, then the étale local ring at `xbar`
is a strict henselization of the henselian local ring at `x`. -/
theorem etaleLocalRing.isStrictHenselizationOf_of_liesOver {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] (xbar : GeometricPoint X) (x : Points X)
    (hx : xbar.liesOver x) :
    -- Local instance justification (proof-local temporary data): Algebra at henselianLocalRing X x is the transport of instAlgebraHenselianLocalRing along hx; a global instance is illegal because hx is not typeclass-synthesizable.
    letI := etaleLocalRing.algebraHenselianLocalRing_of_liesOver xbar hx
    IsStrictHenselizationOf (henselianLocalRing X x) (etaleLocalRing X xbar) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

