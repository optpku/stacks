/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.LocalRing.Basic
public import stacks_project.Chap90.Lemma_90_14_1_SubringOver
public import stacks_project.Chap90.Remarks_90_5_2_Pushforward

/-!
# Coimages in `ArtinianLocalAlgCat` and pushforward on `SubringOver`

The coimage of a morphism `f : A ⟶ B` of residue-identified Artinian local algebras is
the quotient of `A` by `ker f`, bundled in `ArtinianLocalAlgCat`. For `φ : y ⟶ x` in a
category cofibered in groupoids over `C_Λ`, the functor `f_* : S_y ⥤ S_x` pushes an
arrow over a subring of `p.obj y` along the coimage factorization of the composite base
map, using a chosen strongly cocartesian lift.
-/

@[expose] public section

open CategoryTheory IsLocalRing
open Functor

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

namespace ArtinianLocalAlgCat

variable {A B : ArtinianLocalAlgCat Λ k}

/-- Morphisms of residue-identified Artinian local algebras are equal when their
underlying algebra maps are equal. -/
def hom_ext {A B : ArtinianLocalAlgCat Λ k} {f g : A ⟶ B} (h : f.hom = g.hom) : f = g := by
  cases f
  cases g
  subst h
  rfl

/-- The kernel of a morphism of `ArtinianLocalAlgCat` is contained in the maximal ideal. -/
def ker_le_maximalIdeal (f : A ⟶ B) :
    RingHom.ker f.hom.toRingHom ≤ maximalIdeal A.carrier :=
  (Ideal.ker_le_comap f.hom.toRingHom (K := maximalIdeal B.carrier)).trans
    (le_of_eq
      (@maximalIdeal_comap A.carrier B.carrier _ _ _ _ f.hom.toRingHom
        (isLocalHom_toRingHom f.hom)))

/-- The coimage carrier of a morphism of local algebras is nontrivial. -/
instance instNontrivial_kerQuotient (f : A ⟶ B) :
    Nontrivial (A.carrier ⧸ RingHom.ker f.hom.toRingHom) :=
  Ideal.Quotient.nontrivial_iff.mpr
    (mt (fun h => top_le_iff.mp (Eq.trans_le (Eq.symm h) (ker_le_maximalIdeal f)))
      (Ideal.IsMaximal.ne_top (maximalIdeal.isMaximal A.carrier)))

/-- The coimage carrier of a morphism of local algebras is local. -/
instance instIsLocalRing_kerQuotient (f : A ⟶ B) :
    IsLocalRing (A.carrier ⧸ RingHom.ker f.hom.toRingHom) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

/-- Residue identification of the coimage of `f` with `k`, via the third isomorphism
theorem and the residue identification of the domain. -/
noncomputable def imageResidueFieldIso (f : A ⟶ B) :
    ResidueField (A.carrier ⧸ RingHom.ker f.hom.toRingHom) ≃ₐ[Λ] k :=
  (Ideal.quotientEquivAlgOfEq Λ
      (map_maximalIdeal_of_surjective
        (Ideal.Quotient.mk (RingHom.ker f.hom.toRingHom))
        Ideal.Quotient.mk_surjective).symm).trans
    ((DoubleQuot.quotQuotEquivQuotOfLEₐ Λ (ker_le_maximalIdeal f)).trans A.residueFieldIso)

/-- The coimage `A ⧸ ker f` of a morphism of residue-identified Artinian local algebras. -/
noncomputable def image (f : A ⟶ B) : ArtinianLocalAlgCat Λ k :=
  of (A.carrier ⧸ RingHom.ker f.hom.toRingHom) (imageResidueFieldIso f)

/-- The carrier of `image f` is the quotient of the domain by `ker f`. -/
theorem image_carrier (f : A ⟶ B) :
    (image f).carrier = (A.carrier ⧸ RingHom.ker f.hom.toRingHom) := sorry

/-- The canonical surjection from the domain of `f` onto its coimage. -/
noncomputable def toImage (f : A ⟶ B) : A ⟶ image f where
  hom := Ideal.Quotient.mkₐ Λ (RingHom.ker f.hom.toRingHom)
  isLocalHom := sorry
  residue_compat := sorry

/-- The canonical injection of the coimage of `f` into the codomain. -/
noncomputable def imageι (f : A ⟶ B) : image f ⟶ B where
  hom :=
    Ideal.Quotient.liftₐ (RingHom.ker f.hom.toRingHom) f.hom
      (fun _ ha => RingHom.mem_ker.mp ha)
  isLocalHom := sorry
  residue_compat := sorry

/-- The coimage factorization identity `toImage f ≫ imageι f = f`. -/
def image_fac (f : A ⟶ B) : toImage f ≫ imageι f = f :=
  hom_ext
    (Ideal.Quotient.liftₐ_comp (RingHom.ker f.hom.toRingHom) f.hom
      (fun _ ha => RingHom.mem_ker.mp ha))

/-- The coimage projection `toImage f` is surjective. -/
theorem toImage_surjective (f : A ⟶ B) : Function.Surjective (toImage f).hom := sorry

/-- The coimage inclusion `imageι f` is injective. -/
theorem imageι_injective (f : A ⟶ B) : Function.Injective (imageι f).hom := sorry

/-- Commutative squares of `ArtinianLocalAlgCat` induce maps of kernels. -/
def imageMap_le {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    RingHom.ker f.hom.toRingHom ≤ (RingHom.ker g.hom.toRingHom).comap α.hom.toRingHom :=
  fun x hx =>
    Ideal.mem_comap.mpr
      (RingHom.mem_ker.mpr
        ((AlgHom.comp_apply g.hom α.hom x).symm.trans
          ((AlgHom.congr_fun (congrArg Hom.hom h.symm) x).trans
            ((AlgHom.comp_apply β.hom f.hom x).trans
              ((congrArg (fun y => β.hom y) (RingHom.mem_ker.mp hx)).trans
                (map_zero β.hom))))))

/-- The coimage of a morphism of `ArtinianLocalAlgCat` is functorial in commutative squares. -/
noncomputable def imageMap {A₁ B₁ A₂ B₂ : ArtinianLocalAlgCat Λ k}
    (f : A₁ ⟶ B₁) (g : A₂ ⟶ B₂) (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (h : f ≫ β = α ≫ g) :
    image f ⟶ image g where
  hom := Ideal.quotientMapₐ (RingHom.ker g.hom.toRingHom) α.hom (imageMap_le f g α β h)
  isLocalHom := sorry
  residue_compat := sorry

end ArtinianLocalAlgCat

namespace CategoryTheory.Functor

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

/-- The strongly cocartesian property of a bundled lift is a typeclass instance. -/
instance instIsStronglyCocartesian_lift {x : F} {V : ArtinianLocalAlgCat Λ k}
    {f : p.obj x ⟶ V} (l : StronglyCocartesianLift p f) :
    p.IsStronglyCocartesian f l.hom :=
  l.isStronglyCocartesian

/-- A chosen strongly cocartesian lift of the coimage projection of `p.map (a.hom ≫ φ)`. -/
noncomputable def pushforwardLift [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : Over y) :
    StronglyCocartesianLift p (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ))) :=
  StronglyCocartesianLift.ofCleavage (cleavageOp p)
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))

/-- The unique factorization `x' ⟶ x` over the coimage inclusion of `p.map (a.hom ≫ φ)`. -/
noncomputable def pushforwardArrow [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : Over y) : (pushforwardLift p φ a).target ⟶ x :=
  IsStronglyCocartesian.map p
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))
    (pushforwardLift p φ a).hom
    (ArtinianLocalAlgCat.image_fac (p.map (a.hom ≫ φ))).symm
    (a.hom ≫ φ)

/-- The comparison of coimages induced by a morphism of over-objects. -/
def pushforwardSquare {x y : F} (φ : y ⟶ x) {a b : Over y} (η : a ⟶ b) :
    p.map (a.hom ≫ φ) ≫ 𝟙 (p.obj x) = p.map η.left ≫ p.map (b.hom ≫ φ) :=
  (Category.comp_id (p.map (a.hom ≫ φ))).trans
    ((p.congr_map
        ((congrArg (fun k => k ≫ φ) (Over.w η).symm).trans
          (Category.assoc η.left b.hom φ))).trans
      (p.map_comp η.left (b.hom ≫ φ)))

/-- The base morphism of a morphism of pushforward lifts, as a map of coimages. -/
noncomputable def pushforwardMapBase [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    ArtinianLocalAlgCat.image (p.map (a.hom ≫ φ)) ⟶
      p.obj (pushforwardLift p φ b).target :=
  ArtinianLocalAlgCat.imageMap (p.map (a.hom ≫ φ)) (p.map (b.hom ≫ φ))
      (p.map η.left) (𝟙 (p.obj x)) (pushforwardSquare p φ η) ≫
    eqToHom (StronglyCocartesianLift.targetObj (pushforwardLift p φ b)).symm

/-- The identity used to apply the strongly cocartesian universal property to a morphism
of over-objects. -/
theorem pushforwardMap_fac [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    p.map (η.left ≫ (pushforwardLift p φ b).hom) =
      ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)) ≫ pushforwardMapBase p φ η := sorry

/-- The morphism of pushforward targets induced by a morphism of over-objects. -/
noncomputable def pushforwardMap [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    {a b : Over y} (η : a ⟶ b) :
    (pushforwardLift p φ a).target ⟶ (pushforwardLift p φ b).target :=
  IsStronglyCocartesian.map p
    (ArtinianLocalAlgCat.toImage (p.map (a.hom ≫ φ)))
    (pushforwardLift p φ a).hom
    (pushforwardMap_fac p φ η)
    (η.left ≫ (pushforwardLift p φ b).hom)

namespace SubringOver

/-- The functor `f_* : S_y ⥤ S_x` sending a subring-over object to its pushforward along `φ`. -/
noncomputable def pushforward [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x) :
    SubringOver p y ⥤ SubringOver p x where
  obj a :=
    mk (pushforwardArrow p φ a.obj) sorry
  map {a b} η :=
    InducedCategory.homMk (Over.homMk (pushforwardMap p φ η.hom) sorry)
  map_id := sorry
  map_comp := sorry

/-- The domain of `pushforward p φ` applied to `a` lies over the coimage of
`p.map (arrow a ≫ φ)`. -/
theorem pushforward_obj_image [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    p.obj ((pushforward p φ).obj a).obj.left =
      ArtinianLocalAlgCat.image (p.map (arrow a ≫ φ)) := sorry

/-- The underlying arrow of `pushforward p φ` applied to `a` is the cocartesian
factorization of `arrow a ≫ φ`. -/
theorem pushforward_obj_arrow [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    arrow ((pushforward p φ).obj a) = pushforwardArrow p φ a.obj := sorry

/-- The pushforward of an object of `S_y` is an object of `S_x`. -/
theorem pushforward_obj_spec [IsFibered.InGroupoids p.op] {x y : F} (φ : y ⟶ x)
    (a : SubringOver p y) :
    Function.Injective (p.map (arrow ((pushforward p φ).obj a))).hom := sorry

end SubringOver

end CategoryTheory.Functor
