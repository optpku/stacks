module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.CategoryTheory.CommSq
public import ReasLib.RingTheory.Henselian.Henselization
public import ReasLib.RingTheory.Henselian.StrictHenselization
public import ReasLib.RingTheory.RingHom.Local.Map
public import ReasLib.RingTheory.RingHom.Local.Residue
public import stacks_project.Chap66.Lemma_66_22_1_Comparison
public import stacks_project.Chap68.Lemma_68_11_8
public import stacks_project.Chap68.Remark_68_11_11_Pullback
public import stacks_project.Chap68.Remark_68_11_11_Comparison

/-!
# Functoriality of henselian local rings of decent algebraic spaces

An elementary étale neighbourhood of the image point on `Y` pulls back to an
étale `X`-space with a unique point over the given pair, and the resulting
neighbourhood morphism of schemes makes the `Spec` squares of Zariski stalks,
henselizations, and strict henselizations commute.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace CategoryTheory.Limits
open IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} [IsDecent X] [IsDecent Y]
variable (f : X ⟶ Y) {x : Points X} (V : Elementary Y (Points.map f x))

/-- Remark 68.11.11 (1): Let `S` be a scheme and let `f : X ⟶ Y` be a morphism of
decent algebraic spaces over `S`. Let `x : Points X`. If `V` is an elementary étale
neighbourhood of `(Y, Points.map f x)`, then `pullback f V.obj.hom` is étale over
`X` by base change, and it has a unique point `x'` mapping to `x` in `X` and to
`V.obj.point` in `V`. -/
@[stacks 0EPL]
theorem uniqueLift :
    ∃! x' : Points (pullback f V.obj.hom), isLift f V x' :=
  sorry

variable {x' : Points (pullback f V.obj.hom)}
variable (U : Elementary (pullback f V.obj.hom) x')

/-- Remark 68.11.11 (2): After choosing an elementary étale neighbourhood
`(U, u) ⟶ (V ×_Y X, x')` of the unique lift of `(x, V.obj.point)`, the square of
algebraic spaces `U ⟶ V` over `X ⟶ Y` commutes. -/
@[stacks 0EPL]
theorem space_commSq (hx' : isLift f V x') :
    CommSq (ofOverMap (toOverHom (U.obj.hom ≫ pullback.snd f V.obj.hom)))
      (U.obj.hom ≫ pullback.fst f V.obj.hom) V.obj.hom f :=
  sorry

/-- Remark 68.11.11 (3): Chosen henselizations of the Zariski stalks of `U` at `u`
and of `V` at `v` yield a unique local comparison making the `Spec` square over
the stalk map of `schemeHomToBase` commute. The identifications
`O_{X, x}^h = O_{U, u}^h` and `O_{Y, y}^h = O_{V, v}^h` are Lemma 68.11.8. -/
@[stacks 0EPL]
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
      @AlgHom.Local ((V.obj.scheme).presheaf.stalk V.obj.point) RhV RhU _ _ _ _ _,
      CommSq (Spec.map (CommRingCat.ofHom φ.hom.toRingHom))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((U.obj.scheme).presheaf.stalk U.obj.point) RhU)))
        (Spec.map (CommRingCat.ofHom
          (algebraMap ((V.obj.scheme).presheaf.stalk V.obj.point) RhV)))
        (Spec.map (schemeHomToBase_stalkMap f V U hpoint)) :=
  sorry

/-- Remark 68.11.11 (4): Chosen strict henselizations of the Zariski stalks of `U`
at `u` and of `V` at `v`, together with a compatible residue-field map, yield a
unique residue-compatible local comparison making the left `Spec(O^{sh}) ⟶ Spec(O^h)`
square commute over the unique henselization comparison of clause (3). The
identifications `O_{X, x̄} = O_{U, u}^{sh}` and `O_{Y, ȳ} = O_{V, v}^{sh}` are
Properties of Spaces, Lemma 66.22.1. -/
@[stacks 0EPL]
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
      @AlgHom.Local ((V.obj.scheme).presheaf.stalk V.obj.point) RhV RhU _ _ _ _ _)
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
      @AlgHom.Local.ResidueCompatible
        ((V.obj.scheme).presheaf.stalk V.obj.point) RshV RshU _ _ _ _ _ _ _ τ,
      CommSq (Spec.map (CommRingCat.ofHom ψ.toLocal.hom.toRingHom))
        (Spec.map (CommRingCat.ofHom (algebraMap RhU RshU)))
        (Spec.map (CommRingCat.ofHom (algebraMap RhV RshV)))
        (Spec.map (CommRingCat.ofHom φ.hom.toRingHom)) :=
  sorry

/-- A henselization of the Zariski stalk of `V` identifies with the henselian local
ring of `Y` at `Points.map f x`, as in Lemma 68.11.8. -/
theorem nonempty_iso_henselization_base (RhV : Type u) [CommRing RhV]
    [Algebra ((V.obj.scheme).presheaf.stalk V.obj.point) RhV]
    [IsHenselizationOf ((V.obj.scheme).presheaf.stalk V.obj.point) RhV] :
    Nonempty
      ((CommRingCat.universeLift.{u, u + 1}).obj (CommRingCat.of RhV) ≅
        henselianLocalRingCat Y (Points.map f x)) :=
  sorry

/-- A henselization of the Zariski stalk of `U` identifies with the henselian local
ring of `X` at `x`, as in Lemma 68.11.8 applied to the composite neighbourhood
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
centered at `V.obj.point`, as in Properties of Spaces, Lemma 66.22.1. -/
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
centered at `U.obj.point`, as in Properties of Spaces, Lemma 66.22.1. -/
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

end AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
