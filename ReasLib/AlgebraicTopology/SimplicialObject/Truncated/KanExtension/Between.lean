/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Truncated.KanExtension.Pointwise

/-!
# Kan extensions between truncation levels

This leaf owns chosen coskeletons and skeletons from one truncation level to a larger level,
together with their universal map APIs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory.SimplicialObject.Truncated

namespace Between

/-- A truncated simplicial object admits its coskeleton up to a specified larger truncation
level. -/
@[stacks 018B "existence of an objectwise coskeleton between truncation levels"]
abbrev HasCoskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m) : Prop :=
  (SimplexCategory.Truncated.incl n m h).op.HasRightKanExtension U

/-- A truncated simplicial object admits its pointwise coskeleton up to a specified larger
truncation level. -/
@[stacks 018B "pointwise objectwise coskeleton between truncation levels"]
abbrev HasPointwiseCoskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m) : Prop :=
  (SimplexCategory.Truncated.incl n m h).op.HasPointwiseRightKanExtension U

/-- A truncated simplicial object admits its skeleton up to a specified larger truncation
level. -/
@[stacks 018N "existence of an objectwise skeleton between truncation levels"]
abbrev HasSkeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m) : Prop :=
  (SimplexCategory.Truncated.incl n m h).op.HasLeftKanExtension U

/-- A truncated simplicial object admits its pointwise skeleton up to a specified larger
truncation level. -/
@[stacks 018N "pointwise objectwise skeleton between truncation levels"]
abbrev HasPointwiseSkeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m) : Prop :=
  (SimplexCategory.Truncated.incl n m h).op.HasPointwiseLeftKanExtension U

/-- The chosen coskeleton of a truncated simplicial object up to a larger truncation level. -/
@[stacks 018B "chosen objectwise coskeleton between truncation levels"]
noncomputable def coskeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] :
    SimplicialObject.Truncated C m :=
  (SimplexCategory.Truncated.incl n m h).op.rightKanExtension U

namespace coskeleton

/-- The counit of the chosen coskeleton between two truncation levels. -/
@[stacks 018B "counit of an objectwise coskeleton between truncation levels"]
noncomputable def counit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] :
    (SimplexCategory.Truncated.incl n m h).op ⋙ Between.coskeleton U m h ⟶ U :=
  (SimplexCategory.Truncated.incl n m h).op.rightKanExtensionCounit U

/-- The lift to a chosen coskeleton between truncation levels. -/
@[stacks 018B "lift to an objectwise coskeleton between truncation levels"]
noncomputable def lift {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : (SimplexCategory.Truncated.incl n m h).op ⋙ V ⟶ U) :
    V ⟶ Between.coskeleton U m h :=
  Functor.RightKanExtension.lift
    (SimplexCategory.Truncated.incl n m h).op U V f

/-- A coskeleton lift recovers the natural transformation from which it was constructed. -/
@[reassoc (attr := simp), stacks 018B "coskeleton lift on the counit"]
theorem lift_counit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : (SimplexCategory.Truncated.incl n m h).op ⋙ V ⟶ U) :
    (SimplexCategory.Truncated.incl n m h).op.whiskerLeft (lift U m h V f) ≫
        counit U m h =
      f := sorry

/-- The universal Hom-equivalence of a chosen coskeleton between truncation levels. -/
@[stacks 018B "Hom equivalence for an objectwise coskeleton between truncation levels"]
noncomputable def homEquiv {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] (V : SimplicialObject.Truncated C m) :
    (V ⟶ Between.coskeleton U m h) ≃
      ((SimplexCategory.Truncated.incl n m h).op ⋙ V ⟶ U) :=
  Functor.RightKanExtension.homEquiv
    (SimplexCategory.Truncated.incl n m h).op U V

/-- The forward coskeleton Hom-equivalence is restriction followed by the counit. -/
@[simp, stacks 018B "forward coskeleton Hom equivalence"]
theorem homEquiv_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : V ⟶ Between.coskeleton U m h) :
    homEquiv U m h V f =
      (SimplexCategory.Truncated.incl n m h).op.whiskerLeft f ≫ counit U m h := sorry

/-- The inverse coskeleton Hom-equivalence is the universal lift. -/
@[simp, stacks 018B "inverse coskeleton Hom equivalence"]
theorem homEquiv_symm_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : (SimplexCategory.Truncated.incl n m h).op ⋙ V ⟶ U) :
    (homEquiv U m h V).symm f = lift U m h V f := sorry

/-- A morphism of truncated simplicial objects induces a morphism of their chosen coskeletons
between the same truncation levels. -/
@[stacks 018B "map between objectwise coskeletons between truncation levels"]
noncomputable def map {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V : SimplicialObject.Truncated C n}
    [HasCoskeleton U m h] [HasCoskeleton V m h] (f : U ⟶ V) :
    Between.coskeleton U m h ⟶ Between.coskeleton V m h :=
  Functor.RightKanExtension.map
    (SimplexCategory.Truncated.incl n m h).op f

/-- A map of chosen coskeletons between truncation levels commutes with the counits. -/
@[reassoc (attr := simp), stacks 018B "coskeleton map on the counit"]
theorem map_counit {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V : SimplicialObject.Truncated C n}
    [HasCoskeleton U m h] [HasCoskeleton V m h] (f : U ⟶ V) :
    (SimplexCategory.Truncated.incl n m h).op.whiskerLeft (map m h f) ≫
        counit V m h =
      counit U m h ≫ f := sorry

/-- The identity induces the identity map of a chosen coskeleton between truncation levels. -/
@[simp, stacks 018B "identity map of an objectwise coskeleton between truncation levels"]
theorem map_id {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasCoskeleton U m h] :
    map m h (𝟙 U) = 𝟙 (Between.coskeleton U m h) := sorry

/-- Maps of chosen coskeletons between truncation levels respect composition. -/
@[stacks 018B "composition of objectwise coskeleton maps between truncation levels"]
theorem map_comp {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V W : SimplicialObject.Truncated C n}
    [HasCoskeleton U m h] [HasCoskeleton V m h] [HasCoskeleton W m h]
    (f : U ⟶ V) (g : V ⟶ W) :
    map m h (f ≫ g) = map m h f ≫ map m h g := sorry

end coskeleton

/-- The chosen skeleton of a truncated simplicial object up to a larger truncation level. -/
@[stacks 018N "chosen objectwise skeleton between truncation levels"]
noncomputable def skeleton {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] :
    SimplicialObject.Truncated C m :=
  (SimplexCategory.Truncated.incl n m h).op.leftKanExtension U

namespace skeleton

/-- The unit of the chosen skeleton between two truncation levels. -/
@[stacks 018N "unit of an objectwise skeleton between truncation levels"]
noncomputable def unit {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] :
    U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙ Between.skeleton U m h :=
  (SimplexCategory.Truncated.incl n m h).op.leftKanExtensionUnit U

/-- The descent map from a chosen skeleton between truncation levels. -/
@[stacks 018N "descent from an objectwise skeleton between truncation levels"]
noncomputable def desc {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙ V) :
    Between.skeleton U m h ⟶ V :=
  Functor.LeftKanExtension.desc
    (SimplexCategory.Truncated.incl n m h).op U V f

/-- The skeleton unit followed by a descent map recovers the natural transformation from which
the descent map was constructed. -/
@[reassoc (attr := simp), stacks 018N "skeleton unit followed by descent"]
theorem unit_desc {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙ V) :
    unit U m h ≫
        (SimplexCategory.Truncated.incl n m h).op.whiskerLeft (desc U m h V f) =
      f := sorry

/-- The universal Hom-equivalence of a chosen skeleton between truncation levels. -/
@[stacks 018N "Hom equivalence for an objectwise skeleton between truncation levels"]
noncomputable def homEquiv {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] (V : SimplicialObject.Truncated C m) :
    (Between.skeleton U m h ⟶ V) ≃
      (U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙ V) :=
  Functor.LeftKanExtension.homEquiv
    (SimplexCategory.Truncated.incl n m h).op U V

/-- The forward skeleton Hom-equivalence is the unit followed by restriction. -/
@[simp, stacks 018N "forward skeleton Hom equivalence"]
theorem homEquiv_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : Between.skeleton U m h ⟶ V) :
    homEquiv U m h V f =
      unit U m h ≫
        (SimplexCategory.Truncated.incl n m h).op.whiskerLeft f := sorry

/-- The inverse skeleton Hom-equivalence is the universal descent map. -/
@[simp, stacks 018N "inverse skeleton Hom equivalence"]
theorem homEquiv_symm_apply {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] (V : SimplicialObject.Truncated C m)
    (f : U ⟶ (SimplexCategory.Truncated.incl n m h).op ⋙ V) :
    (homEquiv U m h V).symm f = desc U m h V f := sorry

/-- A morphism of truncated simplicial objects induces a morphism of their chosen skeletons
between the same truncation levels. -/
@[stacks 018N "map between objectwise skeletons between truncation levels"]
noncomputable def map {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V : SimplicialObject.Truncated C n}
    [HasSkeleton U m h] [HasSkeleton V m h] (f : U ⟶ V) :
    Between.skeleton U m h ⟶ Between.skeleton V m h :=
  Functor.LeftKanExtension.map
    (SimplexCategory.Truncated.incl n m h).op f

/-- A map of chosen skeletons between truncation levels commutes with the units. -/
@[reassoc (attr := simp), stacks 018N "skeleton map on the unit"]
theorem unit_map {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V : SimplicialObject.Truncated C n}
    [HasSkeleton U m h] [HasSkeleton V m h] (f : U ⟶ V) :
    unit U m h ≫
        (SimplexCategory.Truncated.incl n m h).op.whiskerLeft (map m h f) =
      f ≫ unit V m h := sorry

/-- The identity induces the identity map of a chosen skeleton between truncation levels. -/
@[simp, stacks 018N "identity map of an objectwise skeleton between truncation levels"]
theorem map_id {C : Type u} [Category.{v} C] {n : ℕ}
    (U : SimplicialObject.Truncated C n) (m : ℕ) (h : n ≤ m)
    [HasSkeleton U m h] :
    map m h (𝟙 U) = 𝟙 (Between.skeleton U m h) := sorry

/-- Maps of chosen skeletons between truncation levels respect composition. -/
@[stacks 018N "composition of objectwise skeleton maps between truncation levels"]
theorem map_comp {C : Type u} [Category.{v} C] {n : ℕ}
    (m : ℕ) (h : n ≤ m) {U V W : SimplicialObject.Truncated C n}
    [HasSkeleton U m h] [HasSkeleton V m h] [HasSkeleton W m h]
    (f : U ⟶ V) (g : V ⟶ W) :
    map m h (f ≫ g) = map m h f ≫ map m h g := sorry

end skeleton

/-- The coefficient category admits coskeletons from level `n` to level `m`. -/
@[stacks 018B "existence of coskeletons between truncation levels"]
abbrev HasCoskeletons (C : Type u) [Category.{v} C]
    (n m : ℕ) (h : n ≤ m) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    HasCoskeleton F m h

/-- The coefficient category admits pointwise coskeletons from level `n` to level `m`. -/
@[stacks 018B "pointwise coskeletons between truncation levels"]
abbrev HasPointwiseCoskeletons (C : Type u) [Category.{v} C]
    (n m : ℕ) (h : n ≤ m) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    HasPointwiseCoskeleton F m h

/-- The coefficient category admits skeletons from level `n` to level `m`. -/
@[stacks 018N "existence of skeletons between truncation levels"]
abbrev HasSkeletons (C : Type u) [Category.{v} C]
    (n m : ℕ) (h : n ≤ m) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    HasSkeleton F m h

/-- The coefficient category admits pointwise skeletons from level `n` to level `m`. -/
@[stacks 018N "pointwise skeletons between truncation levels"]
abbrev HasPointwiseSkeletons (C : Type u) [Category.{v} C]
    (n m : ℕ) (h : n ≤ m) : Prop :=
  ∀ F : (SimplexCategory.Truncated n)ᵒᵖ ⥤ C,
    HasPointwiseSkeleton F m h

end Between

end CategoryTheory.SimplicialObject.Truncated
