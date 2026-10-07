module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import stacks_project.Chap59.Lemma_59_104_1_EtaleSheafDescent

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- `f` is an isomorphism over the open complement of a closed immersion `i`. -/
def IsIsoOverComplement {X' X Z : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] : Prop :=
  IsIso (Limits.pullback.fst f (closedImmersionComplement i).ι)

/-- Unfold `IsIsoOverComplement` as an isomorphism of the chosen scheme pullback
projection over `closedImmersionComplement i`. -/
theorem isIsoOverComplement_iff {X' X Z : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    IsIsoOverComplement f i ↔
      IsIso (Limits.pullback.fst f (closedImmersionComplement i).ι) := sorry

/-- Glue of Type-valued small étale sheaves along a cartesian square into the
`2`-fibre product of the pullback functors along the remaining two sides. -/
noncomputable def glueFunctor {X X' Z E : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      CategoricalPullback (pullback j) (pullback g) where
  obj F :=
    { fst := (pullback f).obj F
      snd := (pullback i).obj F
      iso :=
        (pullbackComp f j).app F ≪≫
          (eqToIso (congrArg pullback h_cart.w)).app F ≪≫
          ((pullbackComp i g).symm).app F }
  map α :=
    { fst := (pullback f).map α
      snd := (pullback i).map α
      w := sorry }
  map_id := sorry
  map_comp := sorry

/-- First projection of `glueFunctor` recovers pullback along `f`. -/
noncomputable def glueFunctor_fst {X X' Z E : Scheme.{u}} (f : X' ⟶ X)
    (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ CategoricalPullback.π₁ (pullback j) (pullback g) ≅
      pullback f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- Second projection of `glueFunctor` recovers pullback along `i`. -/
noncomputable def glueFunctor_snd {X X' Z E : Scheme.{u}} (f : X' ⟶ X)
    (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ CategoricalPullback.π₂ (pullback j) (pullback g) ≅
      pullback i :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ sorry)

/-- The stored comparison iso of `glueFunctor` is `pullbackComp` transported
across the cartesian square. -/
theorem glueFunctor_iso {X X' Z E : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((glueFunctor f i j g h_cart).obj F).iso =
      (pullbackComp f j).app F ≪≫
        (eqToIso (congrArg pullback h_cart.w)).app F ≪≫
        ((pullbackComp i g).symm).app F := sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
