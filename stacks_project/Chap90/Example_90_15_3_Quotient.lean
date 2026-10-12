/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Action.Basic
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.CategoryTheory.Endomorphism
public import Mathlib.CategoryTheory.FiberedCategory.HomLift
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.GroupTheory.GroupAction.Defs
public import stacks_project.Chap90.Definition_90_6_2_Predeformation
public import stacks_project.Chap90.Definition_90_12_1_DualNumber
public import stacks_project.Chap90.Definition_90_27_1_MinimalVersal
public import stacks_project.Chap90.«90_15_0_1_TangentSpace»

/-!
# Orbit quotient of restricted coyoneda of dual numbers

The set-valued functor `underline{k[ε]}/G` is the pointwise orbit quotient of
`restrictedCoyoneda (toComplete (dualNumber Λ k))` by a subgroup
`G ≤ Aut (dualNumber Λ k)`. The associated predeformation category is the
Hom-universe lift of its category of elements, matching `identityProjection`.
-/

@[expose] public section

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped BasedFunctor

universe u v w

noncomputable section

namespace ArtinianLocalAlgCat

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/-- The dual numbers `k[ε]` as an object of `CompleteLocalAlgCat Λ k`. -/
abbrev dualNumberComplete : CompleteLocalAlgCat Λ k :=
  toComplete (dualNumber Λ k)

/-- `dualNumberComplete` is `toComplete` of the bundled dual-number object. -/
theorem dualNumberComplete_eq :
    dualNumberComplete Λ k = toComplete (dualNumber Λ k) := sorry

/-- The canonical projection `k[ε] ⟶ k` in `ArtinianLocalAlgCat`. -/
def dualNumberToResidue : dualNumber Λ k ⟶ residue Λ k where
  hom := (fstHom k k k).restrictScalars Λ
  isLocalHom := sorry
  residue_compat := sorry

/-- The underlying algebra map of `dualNumberToResidue` is the coefficient projection. -/
theorem dualNumberToResidue_hom :
    (dualNumberToResidue Λ k).hom = (fstHom k k k).restrictScalars Λ := sorry

/-- Restricted coyoneda of `k[ε]`, i.e. the functor `underline{k[ε]}` on `C_Λ`. -/
abbrev restrictedDualNumber : ArtinianLocalAlgCat Λ k ⥤ Type u :=
  CompleteLocalAlgCat.restrictedCoyoneda (dualNumberComplete Λ k)

/-- On objects, `restrictedDualNumber` is `Hom` out of `dualNumberComplete`. -/
theorem restrictedDualNumber_obj (A : ArtinianLocalAlgCat Λ k) :
    (restrictedDualNumber Λ k).obj A =
      (dualNumberComplete Λ k ⟶ inclusion.obj A) := sorry

variable {Λ k}

/-- Precomposition action of `Aut (dualNumber Λ k)` on `underline{k[ε]}(A)`. -/
def smul (g : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) : (restrictedDualNumber Λ k).obj A :=
  inclusion.map g.symm.hom ≫ x

/-- The automorphism `g` acts by precomposition with `inclusion.map g.symm.hom`. -/
theorem smul_def (g : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) :
    smul g x = inclusion.map g.symm.hom ≫ x := sorry

/-- The identity automorphism acts as the identity. -/
theorem smul_one {A : ArtinianLocalAlgCat Λ k} (x : (restrictedDualNumber Λ k).obj A) :
    smul (1 : Aut (dualNumber Λ k)) x = x := sorry

/-- The action of a product of automorphisms is the composite action. -/
theorem smul_mul (g h : Aut (dualNumber Λ k)) {A : ArtinianLocalAlgCat Λ k}
    (x : (restrictedDualNumber Λ k).obj A) :
    smul (g * h) x = smul g (smul h x) := sorry

/-- Automorphisms of `k[ε]` act on `underline{k[ε]}(A)` by precomposition. -/
instance instMulAction_aut_restrictedDualNumber {A : ArtinianLocalAlgCat Λ k} :
    MulAction (Aut (dualNumber Λ k)) ((restrictedDualNumber Λ k).obj A) where
  smul g x := smul g x
  one_smul := sorry
  mul_smul := sorry

variable (G : Subgroup (Aut (dualNumber Λ k)))

/-- The scalar by which an automorphism of the dual numbers acts on the square-zero
ideal, computed by applying it to ε and taking its infinitesimal coefficient. -/
def epsilonScale (g : Aut (dualNumber Λ k)) : k :=
  (g.hom.hom (TrivSqZeroExt.inr (1 : k))).snd

/-- A derivation of the dual numbers gives the residue-compatible dual-number point
whose scalar coordinate is the residue and whose infinitesimal coordinate is the derivation. -/
def dualNumberPointOfDerivation
    (D : Derivation Λ (dualNumberComplete Λ k).carrier k) :
    (restrictedDualNumber Λ k).obj (dualNumber Λ k) where
  hom := FormalObject.toDualNumber D
  isLocalHom := sorry
  residue_compat := sorry

/-- The orbit relation of `G` on `underline{k[ε]}(A)`. -/
def orbitRel (A : ArtinianLocalAlgCat Λ k) (x y : (restrictedDualNumber Λ k).obj A) :
    Prop :=
  ∃ g : G, g • x = y

/-- Two maps out of `k[ε]` lie in the same `G`-orbit iff some element of `G` carries
one to the other. -/
theorem orbitRel_iff {A : ArtinianLocalAlgCat Λ k}
    (x y : (restrictedDualNumber Λ k).obj A) :
    orbitRel G A x y ↔ ∃ g : G, g • x = y := sorry

/-- Postcomposition with a morphism of `C_Λ` preserves `G`-orbits. -/
theorem orbitRel_map {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    {x y : (restrictedDualNumber Λ k).obj A} (h : orbitRel G A x y) :
    orbitRel G B ((restrictedDualNumber Λ k).map f x)
      ((restrictedDualNumber Λ k).map f y) := sorry

/-- The orbit-quotient functor `underline{k[ε]}/G`. -/
def quotientBy : ArtinianLocalAlgCat Λ k ⥤ Type u where
  obj A := Quot (orbitRel G A)
  map f := TypeCat.ofHom
    (Quot.map ((restrictedDualNumber Λ k).map f) fun _ _ h ↦ orbitRel_map G f h)
  map_id := sorry
  map_comp := sorry

/-- The value of `quotientBy G` at `A` is the quotient of `underline{k[ε]}(A)` by `G`. -/
theorem quotientBy_obj (A : ArtinianLocalAlgCat Λ k) :
    (quotientBy G).obj A = Quot (orbitRel G A) := sorry

/-- Restriction in `quotientBy G` is induced by restriction of representatives. -/
theorem quotientBy_map_mk {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B)
    (x : (restrictedDualNumber Λ k).obj A) :
    (quotientBy G).map f (Quot.mk (orbitRel G A) x) =
      Quot.mk (orbitRel G B) ((restrictedDualNumber Λ k).map f x) := sorry

/-- The quotient map `underline{k[ε]} ⟶ underline{k[ε]}/G`. -/
def quotientMk : restrictedDualNumber Λ k ⟶ quotientBy G where
  app A := TypeCat.ofHom (Quot.mk (orbitRel G A))
  naturality := sorry

/-- The component of `quotientMk` at `A` is `Quot.mk`. -/
theorem quotientMk_app (A : ArtinianLocalAlgCat Λ k)
    (x : (restrictedDualNumber Λ k).obj A) :
    (quotientMk G).app A x = Quot.mk (orbitRel G A) x := sorry

/-- Hom-universe lift of the category of elements of `underline{k[ε]}/G`, matching
the universe constraint of `FormalObject`. -/
abbrev quotientTotal : Type (u + 1) :=
  ULiftHom.{u + 1} (quotientBy G).Elements

/-- `quotientTotal G` is the Hom-universe lift of the category of elements of
`quotientBy G`. -/
theorem quotientTotal_eq :
    quotientTotal G = ULiftHom.{u + 1} (quotientBy G).Elements := sorry

/-- Projection of the Hom-universe lift of `underline{k[ε]}/G` to `C_Λ`. -/
def quotientProjection : quotientTotal G ⥤ ArtinianLocalAlgCat Λ k :=
  (ULiftHom.down : quotientTotal G ⥤ (quotientBy G).Elements) ⋙
    CategoryOfElements.π (quotientBy G)

/-- `quotientProjection` is the category-of-elements projection after Hom-universe
forgetful. -/
theorem quotientProjection_eq :
    quotientProjection G =
      (ULiftHom.down : quotientTotal G ⥤ (quotientBy G).Elements) ⋙
        CategoryOfElements.π (quotientBy G) := sorry

/-- The based functor `underline{k[ε]} ⟶ underline{k[ε]}/G` induced by `quotientMk`. -/
def quotientBasedFunctor :
    BasedCategory.ofFunctor
        (CompleteLocalAlgCat.identityProjection (dualNumberComplete Λ k)) ⥤ᵇ
      BasedCategory.ofFunctor (quotientProjection G) :=
  BasedFunctor.ofFunctor
    ((ULiftHom.down :
        CompleteLocalAlgCat.identityTotal (dualNumberComplete Λ k) ⥤
          (restrictedDualNumber Λ k).Elements) ⋙
      CategoryOfElements.map (quotientMk G) ⋙
      (ULiftHom.up : (quotientBy G).Elements ⥤ quotientTotal G))
    sorry

/-- The underlying total functor of `quotientBasedFunctor` is the Hom-universe lift
of `CategoryOfElements.map (quotientMk G)`. -/
theorem quotientBasedFunctor_eq :
    (quotientBasedFunctor G).toFunctor =
      (ULiftHom.down :
          CompleteLocalAlgCat.identityTotal (dualNumberComplete Λ k) ⥤
            (restrictedDualNumber Λ k).Elements) ⋙
        CategoryOfElements.map (quotientMk G) ⋙
        (ULiftHom.up : (quotientBy G).Elements ⥤ quotientTotal G) := sorry

/-- Stage `n` of `quotientFormalObject`, the image of the identity truncation of
`k[ε]` under `quotientBasedFunctor`. -/
def quotientStage (n : ℕ) : quotientTotal G :=
  (quotientBasedFunctor G).obj
    (CompleteLocalAlgCat.identityStage (dualNumberComplete Λ k) n)

/-- `quotientStage G n` is the image of `identityStage` under `quotientBasedFunctor`. -/
theorem quotientStage_eq (n : ℕ) :
    quotientStage G n =
      (quotientBasedFunctor G).obj
        (CompleteLocalAlgCat.identityStage (dualNumberComplete Λ k) n) := sorry

/-- Successor transition of `quotientStage`. -/
def quotientStageMap (n : ℕ) : quotientStage G (n + 1) ⟶ quotientStage G n :=
  (quotientBasedFunctor G).map
    (CompleteLocalAlgCat.identityStageMap (dualNumberComplete Λ k) n)

/-- `quotientStageMap` is the image of `identityStageMap` under `quotientBasedFunctor`. -/
theorem quotientStageMap_eq (n : ℕ) :
    quotientStageMap G n =
      (quotientBasedFunctor G).map
        (CompleteLocalAlgCat.identityStageMap (dualNumberComplete Λ k) n) := sorry

/-- The formal object of `underline{k[ε]}/G` obtained by pushing identity truncations
of `k[ε]` along `quotientBasedFunctor`. -/
def quotientFormalObject : FormalObject (quotientProjection G) where
  base := dualNumberComplete Λ k
  system := Functor.ofOpSequence (quotientStageMap G)
  over_obj := sorry
  over_step := sorry

/-- The complete local base of `quotientFormalObject G` is `dualNumberComplete`. -/
theorem quotientFormalObject_base :
    (quotientFormalObject G).base = dualNumberComplete Λ k := sorry

/-- `quotientBasedFunctor G` represents `quotientFormalObject G`. -/
theorem quotientFormalObject_represents :
    FormalObject.Represents (quotientFormalObject G) (quotientBasedFunctor G) := sorry

/-- The Hom-universe lift of the category of elements of `underline{k[ε]}/G` is
cofibered in groupoids over `C_Λ`. -/
instance instIsFiberedInGroupoids_quotientProjection_op :
    Functor.IsFibered.InGroupoids (quotientProjection G).op := sorry

/-- The dual-number fibre object of `quotientProjection G` with component `q`. -/
def orbitQuotientElement (q : Quot (orbitRel G (dualNumber Λ k))) : quotientTotal G :=
  ULiftHom.objUp ⟨dualNumber Λ k, q⟩

/-- `orbitQuotientElement G q` lies over `dualNumber`. -/
theorem orbitQuotientElement_obj (q : Quot (orbitRel G (dualNumber Λ k))) :
    (quotientProjection G).obj (orbitQuotientElement G q) = dualNumber Λ k := sorry

end ArtinianLocalAlgCat

namespace CategoryTheory.Functor

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]

/-- A functor `p : F ⥤ ArtinianLocalAlgCat Λ k` satisfies Schlessinger's condition (S2)
if every cospan in `F` lying over `A ⟶ k ← k[ε]` completes to a commutative square whose
image is a pullback, and any two such completions admit a fibre morphism identifying
the legs to the object over `A`. -/
class HasSchlessingerS2 (p : F ⥤ ArtinianLocalAlgCat Λ k) : Prop where
  /-- Completions exist for cospans lying over `A ⟶ k ← k[ε]`. -/
  exists_completion : ∀ {x x0 xε : F} (d : x ⟶ x0) (e : xε ⟶ x0),
    p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
      ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xε),
        CommSq a c d e ∧
          IsPullback (p.map a) (p.map c) (p.map d) (p.map e)
  /-- Two completions over the same dual-number fibre product admit a fibre map identifying
  the legs to the object over `A`. -/
  exists_vertical : ∀ {x x0 xε y y' : F} (d : x ⟶ x0) (e : xε ⟶ x0)
      (a : y ⟶ x) (c : y ⟶ xε) (a' : y' ⟶ x) (c' : y' ⟶ xε),
    p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
      CommSq a c d e →
      CommSq a' c' d e →
      IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
      p.obj y = p.obj y' →
      p.IsHomLift (p.map a) a' →
      p.IsHomLift (p.map c) c' →
        ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a

/-- The identity functor on `ArtinianLocalAlgCat Λ k` satisfies (S2). -/
instance instHasSchlessingerS2Id :
    HasSchlessingerS2 (𝟭 (ArtinianLocalAlgCat Λ k)) := sorry

/-- Condition (S2) is dual-number diagram completion together with existence of a fibre
morphism identifying the legs to the object over `A`. -/
theorem hasSchlessingerS2_spec (p : F ⥤ ArtinianLocalAlgCat Λ k) :
    HasSchlessingerS2 p ↔
      (∀ {x x0 xε : F} (d : x ⟶ x0) (e : xε ⟶ x0),
          p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
            ∃ (y : F) (a : y ⟶ x) (c : y ⟶ xε),
              CommSq a c d e ∧
                IsPullback (p.map a) (p.map c) (p.map d) (p.map e)) ∧
        ∀ {x x0 xε y y' : F} (d : x ⟶ x0) (e : xε ⟶ x0)
            (a : y ⟶ x) (c : y ⟶ xε) (a' : y' ⟶ x) (c' : y' ⟶ xε),
          p.IsHomLift (ArtinianLocalAlgCat.dualNumberToResidue Λ k) e →
            CommSq a c d e →
            CommSq a' c' d e →
            IsPullback (p.map a) (p.map c) (p.map d) (p.map e) →
            p.obj y = p.obj y' →
            p.IsHomLift (p.map a) a' →
            p.IsHomLift (p.map c) c' →
              ∃ b : y ⟶ y', p.IsHomLift (𝟙 (p.obj y)) b ∧ b ≫ a' = a := sorry

end CategoryTheory.Functor

end
