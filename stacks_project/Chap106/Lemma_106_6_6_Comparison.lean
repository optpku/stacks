/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap73.Definition_73_4_1_Precoverage
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap106.Definition_106_3_1_Thickening

/-!
# Étale-local comparison of smooth cartesian lifts

Inverse images of a thickening of algebraic spaces are compared by `IsPullback`
of the opposite square on the chosen pullback, and 2-cells over `W` are
restricted by whiskering and `toGroupoids.map` transports.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Bicategory FiberedCategoryOver
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.Lift

variable {S : Scheme.{u}}

/-- The composition comparison for `AlgebraicSpace.toGroupoids.map`, obtained
from the `map_comp` fields of `Sets.ofPresheaf` and `Sets.toGroupoids`. -/
def mapCompIso {U V W : AlgebraicSpace S} (f : U ⟶ V) (g : V ⟶ W) :
    AlgebraicSpace.toGroupoids.map (f ≫ g) ≅
      AlgebraicSpace.toGroupoids.map f ≫ AlgebraicSpace.toGroupoids.map g :=
  eqToIso <|
    (congrArg (Sets.toGroupoids (Over S)).map
        ((Sets.ofPresheaf (Over S)).map_comp f g)).trans
      ((Sets.toGroupoids (Over S)).map_comp
        ((Sets.ofPresheaf (Over S)).map f) ((Sets.ofPresheaf (Over S)).map g))

/-- Transport `AlgebraicSpace.toGroupoids.map` along an equality of algebraic-space
morphisms. -/
def mapCongrIso {U V : AlgebraicSpace S} {f g : U ⟶ V} (h : f = g) :
    AlgebraicSpace.toGroupoids.map f ≅ AlgebraicSpace.toGroupoids.map g :=
  eqToIso (congrArg AlgebraicSpace.toGroupoids.map h)

/-- `mapCompIso f g` identifies `toGroupoids.map (f ≫ g)` with the composite
of `toGroupoids.map f` and `toGroupoids.map g`. -/
theorem mapCompIso_spec {U V W : AlgebraicSpace S} (f : U ⟶ V) (g : V ⟶ W) :
    mapCompIso f g =
      eqToIso
        ((congrArg (Sets.toGroupoids (Over S)).map
            ((Sets.ofPresheaf (Over S)).map_comp f g)).trans
          ((Sets.toGroupoids (Over S)).map_comp
            ((Sets.ofPresheaf (Over S)).map f)
            ((Sets.ofPresheaf (Over S)).map g))) :=
  sorry

/-- `mapCongrIso h` is transport of `toGroupoids.map` along `h`. -/
theorem mapCongrIso_spec {U V : AlgebraicSpace S} {f g : U ⟶ V} (h : f = g) :
    mapCongrIso h = eqToIso (congrArg AlgebraicSpace.toGroupoids.map h) :=
  sorry

variable {X X' : GroupoidsOver S}
variable {W W' W'' : AlgebraicSpace S}
variable {x : W.toGroupoids ⟶ X}
variable {x' : W'.toGroupoids ⟶ X'}
variable {x'' : W''.toGroupoids ⟶ X'}
variable {iX : X ⟶ X'}
variable {i : W ⟶ W'} {i'' : W ⟶ W''}

/-- The 2-morphism over `W` obtained from commutativity of the initial diagram,
as the composite `α'.symm ≪≫ α''`. -/
def overWIso (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'') :
    AlgebraicSpace.toGroupoids.map i ≫ x' ≅
      AlgebraicSpace.toGroupoids.map i'' ≫ x'' :=
  α'.symm ≪≫ α''

/-- `overWIso` is the pasting `α'.symm ≪≫ α''`. -/
theorem overWIso_spec (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'') :
    overWIso α' α'' = α'.symm ≪≫ α'' :=
  sorry

section InverseImage

variable {U : AlgebraicSpace S} {f' : U ⟶ W'} {f'' : U ⟶ W''}

/-- Restriction of a 2-cell `γ : toGroupoids.map f'' ≫ x'' ≅ toGroupoids.map f' ≫ x'`
to the inverse image `(f')⁻¹(W)`, as left whiskering by
`toGroupoids.map (pullback.snd i f')` reassociated to a binary composite. -/
def restrictGamma
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x') :
    (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f'') ≫ x'' ≅
      (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f') ≫ x' :=
  (α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
      (AlgebraicSpace.toGroupoids.map f'') x'').symm ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.snd i f')) γ ≪≫
    α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
      (AlgebraicSpace.toGroupoids.map f') x'

/-- `restrictGamma` is left whiskering of `γ` by
`toGroupoids.map (pullback.snd i f')`, reassociated to a binary composite. -/
theorem restrictGamma_spec
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x') :
    restrictGamma γ =
      (α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
          (AlgebraicSpace.toGroupoids.map f'') x'').symm ≪≫
        whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.snd i f')) γ ≪≫
        α_ (AlgebraicSpace.toGroupoids.map (pullback.snd i f'))
          (AlgebraicSpace.toGroupoids.map f') x' :=
  sorry

/-- Restriction of the original over-`W` 2-morphism to `(f')⁻¹(W)`, transported
along `pullback.condition` and the inverse-image commuting equality so that it
lands in the same 2-cell type as `restrictGamma`. -/
def restrictOverW (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f'') ≫ x'' ≅
      (AlgebraicSpace.toGroupoids.map (pullback.snd i f') ≫
        AlgebraicSpace.toGroupoids.map f') ≫ x' :=
  whiskerRightIso
      (mapCompIso (pullback.snd i f') f'').symm x'' ≪≫
    whiskerRightIso (mapCongrIso h_comm.symm) x'' ≪≫
    whiskerRightIso (mapCompIso (pullback.fst i f') i'') x'' ≪≫
    α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (AlgebraicSpace.toGroupoids.map i'') x'' ≪≫
    whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (overWIso α' α'').symm ≪≫
    (α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
      (AlgebraicSpace.toGroupoids.map i) x').symm ≪≫
    whiskerRightIso (mapCompIso (pullback.fst i f') i).symm x' ≪≫
    whiskerRightIso (mapCongrIso (pullback.condition : pullback.fst i f' ≫ i = pullback.snd i f' ≫ f')) x' ≪≫
    whiskerRightIso (mapCompIso (pullback.snd i f') f') x'

/-- `restrictOverW` is the transport of left whiskering of `overWIso.symm` along
the inverse-image commuting equality and `pullback.condition`. -/
theorem restrictOverW_spec (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    restrictOverW α' α'' h_comm =
      whiskerRightIso
          (mapCompIso (pullback.snd i f') f'').symm x'' ≪≫
        whiskerRightIso (mapCongrIso h_comm.symm) x'' ≪≫
        whiskerRightIso (mapCompIso (pullback.fst i f') i'') x'' ≪≫
        α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (AlgebraicSpace.toGroupoids.map i'') x'' ≪≫
        whiskerLeftIso (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (overWIso α' α'').symm ≪≫
        (α_ (AlgebraicSpace.toGroupoids.map (pullback.fst i f'))
          (AlgebraicSpace.toGroupoids.map i) x').symm ≪≫
        whiskerRightIso (mapCompIso (pullback.fst i f') i).symm x' ≪≫
        whiskerRightIso (mapCongrIso (pullback.condition : pullback.fst i f' ≫ i = pullback.snd i f' ≫ f')) x' ≪≫
        whiskerRightIso (mapCompIso (pullback.snd i f') f') x' :=
  sorry

/-- Clause (c): the restriction of `γ` to `(f')⁻¹(W)` equals the restriction of
the original over-`W` 2-morphism. -/
def RestrictsToOverW (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') : Prop :=
  restrictGamma γ = restrictOverW α' α'' h_comm

/-- `RestrictsToOverW` is equality of `restrictGamma` with `restrictOverW`. -/
theorem RestrictsToOverW_iff (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    (γ : AlgebraicSpace.toGroupoids.map f'' ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map f' ≫ x')
    (h_comm : pullback.fst i f' ≫ i'' = pullback.snd i f' ≫ f'') :
    RestrictsToOverW α' α'' γ h_comm ↔ restrictGamma γ = restrictOverW α' α'' h_comm :=
  sorry

/-- Clauses (a) and (b): the chosen inverse image `(f')⁻¹(W)` is a pullback of
`i''` along `f''` if and only if it is isomorphic to `(f'')⁻¹(W)` over both
`U` and `W`. -/
theorem sameInverseImage_iff :
    IsPullback (pullback.fst i f') (pullback.snd i f') i'' f'' ↔
      ∃ e : pullback i f' ≅ pullback i'' f'',
        e.hom ≫ pullback.snd i'' f'' = pullback.snd i f' ∧
          e.hom ≫ pullback.fst i'' f'' = pullback.fst i f' :=
  sorry

end InverseImage

/-- An étale covering `{f' k : Wk k ⟶ W'}` together with étale maps
`f'' k : Wk k ⟶ W''` and 2-isomorphisms `γ k` compares two smooth cartesian
lifts étale-locally: inverse images of `W` agree, the two maps restrict
equally there, and each `γ k` restricts to the original over-`W` 2-morphism. -/
def IsEtaleLocalIso (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    {ι : Type u} {Wk : ι → AlgebraicSpace S}
    (f' : ∀ k, Wk k ⟶ W') (f'' : ∀ k, Wk k ⟶ W'')
    (γ : ∀ k, AlgebraicSpace.toGroupoids.map (f'' k) ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map (f' k) ≫ x') : Prop :=
  AlgebraicSpace.EtaleCovering (fun k ↦ Over.mk (f' k)) ∧
    (∀ k, AlgebraicSpace.Etale (f'' k)) ∧
    (∀ k, IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k)) i'' (f'' k)) ∧
    (∀ k (hPB : IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k))
        i'' (f'' k)),
      RestrictsToOverW α' α'' (γ k) hPB.w)

/-- `IsEtaleLocalIso` unpacks as an étale covering of `W'`, étaleness of each
`f'' k`, inverse-image pullback squares, and restriction of each `γ k` to the
over-`W` 2-morphism. -/
theorem IsEtaleLocalIso_iff (α' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i ≫ x')
    (α'' : x ≫ iX ≅ AlgebraicSpace.toGroupoids.map i'' ≫ x'')
    {ι : Type u} {Wk : ι → AlgebraicSpace S}
    (f' : ∀ k, Wk k ⟶ W') (f'' : ∀ k, Wk k ⟶ W'')
    (γ : ∀ k, AlgebraicSpace.toGroupoids.map (f'' k) ≫ x'' ≅
      AlgebraicSpace.toGroupoids.map (f' k) ≫ x') :
    IsEtaleLocalIso α' α'' f' f'' γ ↔
      AlgebraicSpace.EtaleCovering (fun k ↦ Over.mk (f' k)) ∧
        (∀ k, AlgebraicSpace.Etale (f'' k)) ∧
        (∀ k, IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k))
            i'' (f'' k)) ∧
        (∀ k (hPB : IsPullback (pullback.fst i (f' k)) (pullback.snd i (f' k))
            i'' (f'' k)),
          RestrictsToOverW α' α'' (γ k) hPB.w) :=
  sorry

end AlgebraicGeometry.AlgebraicStack.Lift
