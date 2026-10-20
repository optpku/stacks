module

public import Mathlib.Algebra.Algebra.Tower
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Henselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Functoriality
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.StrictHenselization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import ReasLib.RingTheory.Henselian.Henselization.Comparison
public import ReasLib.RingTheory.Henselian.StrictHenselization.Comparison
public import ReasLib.RingTheory.RingHom.Local.Residue

/-!
# Local-ring comparisons along elementary étale neighbourhood maps

A pointed pullback neighbourhood gives compatible maps on Zariski stalks,
henselizations, and geometric strict henselizations, identifying the resulting
diagram with the henselian and étale local rings of the original spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
variable (f : X ⟶ Y) {x : Points X} (V : Elementary Y (Points.map f x))
variable {x' : Points (pullback f V.obj.hom)}
variable (U : Elementary (pullback f V.obj.hom) x')

/-- Henselizations of two neighbourhood stalks admit a unique local comparison
whose spectrum commutes with the pointed scheme stalk square. -/
theorem henselization_existsUnique (hx' : isLift f V x')
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point)
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point)
      ((U.obj.scheme).presheaf.stalk U.obj.point)]
    (hAlg :
      algebraMap ((V.obj.scheme).presheaf.stalk V.obj.point)
          ((U.obj.scheme).presheaf.stalk U.obj.point) =
        schemeHomToBase_stalkHom f V U hpoint)
    [IsLocalHom (schemeHomToBase_stalkHom f V U hpoint)]
    (RhV : Type u) [CommRing RhV]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RhV]
    [IsHenselizationOf ((V.obj.scheme).presheaf.stalk V.obj.point) RhV]
    (RhU : Type u) [CommRing RhU]
    [Algebra ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    [IsHenselizationOf ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RhU]
    [IsScalarTower ((V.obj.scheme).presheaf.stalk V.obj.point)
      ((U.obj.scheme).presheaf.stalk U.obj.point) RhU] :
    ∃! φ :
      AlgHom.Local (R := (V.obj.scheme).presheaf.stalk V.obj.point)
        (A := RhV) (B := RhU),
      CommSq (Spec.map (CommRingCat.ofHom φ.hom.toRingHom))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((U.obj.scheme).presheaf.stalk U.obj.point) RhU)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((V.obj.scheme).presheaf.stalk V.obj.point) RhV)))
        (Spec.map (schemeHomToBase_stalkMap f V U hpoint)) :=
  sorry

/-- Strict henselizations of two neighbourhood stalks admit a unique local
comparison with prescribed compatible residue map, commuting with the chosen
henselization comparison on spectra. -/
theorem strictHenselization_existsUnique (hx' : isLift f V x')
    (hpoint : schemeHomToBase f V U U.obj.point = V.obj.point)
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point)
      ((U.obj.scheme).presheaf.stalk U.obj.point)]
    (hAlg :
      algebraMap ((V.obj.scheme).presheaf.stalk V.obj.point)
          ((U.obj.scheme).presheaf.stalk U.obj.point) =
        schemeHomToBase_stalkHom f V U hpoint)
    [IsLocalHom (schemeHomToBase_stalkHom f V U hpoint)]
    (RhV : Type u) [CommRing RhV]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RhV]
    [IsHenselizationOf ((V.obj.scheme).presheaf.stalk V.obj.point) RhV]
    (RhU : Type u) [CommRing RhU]
    [Algebra ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    [IsHenselizationOf ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RhU]
    [IsScalarTower ((V.obj.scheme).presheaf.stalk V.obj.point)
      ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    (φ :
      AlgHom.Local (R := (V.obj.scheme).presheaf.stalk V.obj.point)
        (A := RhV) (B := RhU))
    (RshV : Type u) [CommRing RshV]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RshV]
    [IsStrictHenselizationOf ((V.obj.scheme).presheaf.stalk V.obj.point) RshV]
    [Algebra RhV RshV]
    [IsScalarTower ((V.obj.scheme).presheaf.stalk V.obj.point) RhV RshV]
    (RshU : Type u) [CommRing RshU]
    [Algebra ((U.obj.scheme).presheaf.stalk U.obj.point) RshU]
    [IsStrictHenselizationOf ((U.obj.scheme).presheaf.stalk U.obj.point) RshU]
    [Algebra RhU RshU]
    [IsScalarTower ((U.obj.scheme).presheaf.stalk U.obj.point) RhU RshU]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RshU]
    [IsScalarTower ((V.obj.scheme).presheaf.stalk V.obj.point)
      ((U.obj.scheme).presheaf.stalk U.obj.point) RshU]
    (τ : ResidueField RshV →+* ResidueField RshU)
    (hτ :
      ResidueField.Compatible (schemeHomToBase_stalkHom f V U hpoint)
        (algebraMap ((V.obj.scheme).presheaf.stalk V.obj.point) RshV)
        (algebraMap ((U.obj.scheme).presheaf.stalk U.obj.point) RshU) τ) :
    ∃! ψ :
      AlgHom.Local.ResidueCompatible
        (R := (V.obj.scheme).presheaf.stalk V.obj.point) (A := RshV) (B := RshU) τ,
      CommSq (Spec.map (CommRingCat.ofHom ψ.toLocal.hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (algebraMap RhU RshU)))
        (Spec.map (CommRingCat.ofHom (algebraMap RhV RshV)))
        (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)) :=
  sorry

/-- A henselization of the Zariski stalk of `U` identifies with the henselian local
ring of `X` at `x`, using the composite elementary neighbourhood
`U ⟶ X`. -/
theorem nonempty_iso_henselization_source (hx' : isLift f V x') (RhU : Type u)
    [CommRing RhU]
    [Algebra ((U.obj.scheme).presheaf.stalk U.obj.point) RhU]
    [IsHenselizationOf ((U.obj.scheme).presheaf.stalk U.obj.point) RhU] :
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of RhU) ≅
        henselianLocalRingCat X x) :=
  sorry

/-- A strict henselization of the Zariski stalk of `V` identifies with the étale
local ring of `Y` at a geometric point obtained from a geometric point of `V`
centered at `V.obj.point`. -/
theorem nonempty_iso_etaleLocalRing_base
    (vbar : Scheme.GeometricPoint V.obj.scheme)
    (hv_center : vbar.image = V.obj.point) (ybar : GeometricPoint Y)
    (hy : (GeometricPoint.ofScheme vbar).map V.obj.hom = ybar)
    (RshV : Type u) [CommRing RshV]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RshV]
    [IsStrictHenselizationOf ((V.obj.scheme).presheaf.stalk V.obj.point) RshV] :
    Nonempty (etaleLocalRing Y ybar ≃+* RshV) :=
  sorry

/-- A strict henselization of the Zariski stalk of `U` identifies with the étale
local ring of `X` at a geometric point obtained from a geometric point of `U`
centered at `U.obj.point`. -/
theorem nonempty_iso_etaleLocalRing_source (hx' : isLift f V x')
    (ubar : Scheme.GeometricPoint U.obj.scheme)
    (hu_center : ubar.image = U.obj.point) (xbar : GeometricPoint X)
    (hxbar :
      (GeometricPoint.ofScheme ubar).map
          (U.obj.hom ≫ pullback.fst f V.obj.hom) =
        xbar)
    (RshU : Type u) [CommRing RshU]
    [Algebra ((U.obj.scheme).presheaf.stalk U.obj.point) RshU]
    [IsStrictHenselizationOf ((U.obj.scheme).presheaf.stalk U.obj.point) RshU] :
    Nonempty (etaleLocalRing X xbar ≃+* RshU) :=
  sorry

set_option maxHeartbeats 800000 in
/-- An elementary neighbourhood of the image of a point has an étale pullback
with a unique pointed lift. Every elementary neighbourhood of this lift gives
simultaneously commuting scheme, Zariski stalk, henselian, and strict henselian
squares. The comparisons identify the henselian vertical map with pullback on
henselian local rings and the horizontal maps with their canonical geometric
germs, and the strict identifications preserve the canonical Zariski-stalk
comparison maps; the strict vertical map pulls back every geometric-point germ. -/
theorem functoriality {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] [IsDecent Y] (f : X ⟶ Y) {x : Points X}
    (V : Elementary Y (Points.map f x)) :
    Etale (pullback.fst f V.obj.hom) ∧
      ∃ x' : Points (pullback f V.obj.hom),
        isLift f V x' ∧ (∀ z, isLift f V z → z = x') ∧
        ∀ U : Elementary (pullback f V.obj.hom) x',
          let RV := V.obj.scheme.presheaf.stalk V.obj.point
          let RU := U.obj.scheme.presheaf.stalk U.obj.point
          ∃ hpoint : schemeHomToBase f V U U.obj.point = V.obj.point,
            CommSq (U.obj.hom ≫ pullback.snd f V.obj.hom)
              (U.obj.hom ≫ pullback.fst f V.obj.hom) V.obj.hom f ∧
            CommSq (Spec.map (schemeHomToBase_stalkMap f V U hpoint))
              (Scheme.fromSpecStalk U.obj.scheme U.obj.point)
              (Scheme.fromSpecStalk V.obj.scheme V.obj.point)
              (schemeHomToBase f V U) ∧
            ∀ (ubar : Scheme.GeometricPoint U.obj.scheme)
              (hu : ubar.image = U.obj.point),
              let vbar := ubar.map (schemeHomToBase f V U)
              let xbar := (GeometricPoint.ofScheme ubar).map
                (U.obj.hom ≫ pullback.fst f V.obj.hom)
              let ybar := (GeometricPoint.ofScheme vbar).map V.obj.hom
              ∃ (hx : xbar.image = x) (hy : ybar.image = Points.map f x),
                vbar.image = V.obj.point ∧ xbar.map f = ybar ∧
                ∃ (RhV : Type u) (_ : CommRing RhV)
                  (_ : Algebra RV RhV)
                  (_ : IsHenselizationOf RV RhV)
                  (RhU : Type u) (_ : CommRing RhU)
                  (_ : Algebra RU RhU)
                  (_ : IsHenselizationOf RU RhU)
                  (RshV : Type u) (_ : CommRing RshV)
                  (_ : Algebra RV RshV)
                  (_ : IsStrictHenselizationOf RV RshV)
                  (RshU : Type u) (_ : CommRing RshU)
                  (_ : Algebra RU RshU)
                  (_ : IsStrictHenselizationOf RU RshU)
                  (φh : RhV →+* RhU) (φs : RshV →+* RshU)
                  (iV : RhV →+* RshV) (iU : RhU →+* RshU)
                  (eHV : ULift.{u + 1} RhV ≃+* henselianLocalRing Y (Points.map f x))
                  (eHU : ULift.{u + 1} RhU ≃+* henselianLocalRing X x)
                  (eSV : RshV ≃+* etaleLocalRing Y ybar)
                  (eSU : RshU ≃+* etaleLocalRing X xbar)
                  (σ : etaleLocalRing Y ybar →+* etaleLocalRing X xbar)
                  (τ : ResidueField RshV →+* ResidueField RshU),
                  IsLocalHom φh ∧ IsLocalHom φs ∧
                  IsLocalHom iV ∧ IsLocalHom iU ∧ IsLocalHom σ ∧
                  iV.comp (algebraMap RV RhV) =
                    algebraMap RV RshV ∧
                  iU.comp (algebraMap RU RhU) =
                    algebraMap RU RshU ∧
                  φh.comp (algebraMap RV RhV) =
                    (algebraMap RU RhU).comp
                      (schemeHomToBase_stalkHom f V U hpoint) ∧
                  φs.comp iV = iU.comp φh ∧
                  eHU.toRingHom.comp φh.ulift =
                    (HenselianFunctoriality.map f x (Points.map f x) rfl).comp
                      eHV.toRingHom ∧
                  eSV.toRingHom.comp (algebraMap RV RshV) =
                    ((by
                      exact (Scheme.GeometricPoint.map_image ubar
                        (schemeHomToBase f V U)).trans
                          ((congrArg (schemeHomToBase f V U) hu).trans hpoint) :
                      vbar.image = V.obj.point) ▸
                        etaleLocalRing_etaleNeighborhood.fromZariskiStalk
                          (GeometricPoint.SmallEtaleNeighborhood.of
                            (xbar := ybar) V.obj.toSite
                            (Over.homMk vbar.hom rfl) rfl) :
                      V.obj.scheme.presheaf.stalk V.obj.point →+* etaleLocalRing Y ybar) ∧
                  eSU.toRingHom.comp (algebraMap RU RshU) =
                    (hu ▸ etaleLocalRing_etaleNeighborhood.fromZariskiStalk
                      (GeometricPoint.SmallEtaleNeighborhood.of (xbar := xbar)
                        (smallEtaleSite.mk (U.obj.hom ≫ pullback.fst f V.obj.hom)
                          (MorphismProperty.comp_mem (@Etale S) _ _
                            (EtaleNeighborhood.spec U.obj).1
                            (Etale.pullback_fst f (EtaleNeighborhood.spec V.obj).1)))
                        (Over.homMk ubar.hom rfl) rfl) :
                      U.obj.scheme.presheaf.stalk U.obj.point →+* etaleLocalRing X xbar) ∧
                  eSV.toRingHom.comp iV =
                    (hy ▸ etaleLocalRing.fromHenselianLocalRing ybar).comp
                      (eHV.toRingHom.comp ULift.ringEquiv.symm.toRingHom) ∧
                  eSU.toRingHom.comp iU =
                    (hx ▸ etaleLocalRing.fromHenselianLocalRing xbar).comp
                      (eHU.toRingHom.comp ULift.ringEquiv.symm.toRingHom) ∧
                  eSU.toRingHom.comp φs = σ.comp eSV.toRingHom ∧
                  (residue RshU).comp φs = τ.comp (residue RshV) ∧
                  ResidueField.Compatible (schemeHomToBase_stalkHom f V U hpoint)
                    (algebraMap RV RshV)
                    (algebraMap RU RshU) τ ∧
                  ∀ (N : smallEtaleSite Y) (lY : GeometricPoint.OverLift ybar N),
                    ∃ (M : smallEtaleSite X) (m : M.left ⟶ N.left)
                      (lX : GeometricPoint.OverLift xbar M),
                      ofOverMap m ≫ N.hom = M.hom ≫ f ∧
                      lX.hom.left ≫ m.left = lY.hom.left ∧
                      ∀ s : Γ(N.left.left, ⊤),
                        σ (RingCat.Hom.hom
                          ((eqToHom (structureSheaf_obj N).symm) ≫
                            (GeometricPoint.toSmallEtalePoint ybar).toPresheafFiber
                              N lY (structureSheaf Y).obj) s) =
                          RingCat.Hom.hom
                            ((eqToHom (structureSheaf_obj M).symm) ≫
                              (GeometricPoint.toSmallEtalePoint xbar).toPresheafFiber
                                M lX (structureSheaf X).obj)
                            ((Scheme.Γ.map m.left.op).hom s) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
