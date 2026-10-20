module

public import ReasLib.CategoryTheory.Monoidal.Bimod.Adjunction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projection formula for relative tensor products

Let `L ⊣ R` be a monoidal adjunction satisfying the projection formula.  A right module `M`
over `R(A)` has a lower shriek over `A`.  For an `(A,B)`-bimodule `N`, the projection formula
identifies tensoring that lower shriek with lower-shrieking the relative tensor of `M` and the
transport of `N` by `R`.

The comparison is constructed from the coequalizers defining balanced tensor products.  This
file exposes the objectwise comparison and its inverse, then packages their naturality in both
module variables as an isomorphism of curried bifunctors.
-/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] [MonoidalCategory C]
variable {D : Type uD} [Category.{vD} D] [MonoidalCategory D]
variable {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
variable [R.LaxMonoidal] [L.OplaxMonoidal] [adj.IsMonoidal]
variable [adj.ProjectionFormulaMap]

namespace RelativeTensor

section Comparison

variable [HasCoequalizers C] [HasCoequalizers D]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable (A B : Mon D)
variable (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod A B)

/-- The map on unbalanced tensors underlying the relative-tensor projection formula.  It is the
ambient projection-formula isomorphism followed by the image of the localized quotient map. -/
@[stacks 0FRB "relative tensor comparison on unbalanced tensors"]
noncomputable def comparisonAux :
    ((adj.rightModuleLowerShriek A).obj M).X ⊗ N.X ⟶
      ((adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N))).X :=
  (adj.projectionFormulaMapIso M.X N.X).hom ≫
    L.map (coequalizer.π
      (M.actRight ▷ ((R.mapBimod A B).obj N).X)
      ((α_ M.X (R.mapMon.obj A).X ((R.mapBimod A B).obj N).X).hom ≫
        (M.X ◁ ((R.mapBimod A B).obj N).actLeft)))

/-- The unbalanced comparison coequalizes the ambient `A`-actions. -/
theorem comparisonAux_condition :
    (((adj.rightModuleLowerShriek A).obj M).actRight ▷ N.X) ≫
        comparisonAux adj A B M N =
      ((α_ ((adj.rightModuleLowerShriek A).obj M).X A.X N.X).hom ≫
        (((adj.rightModuleLowerShriek A).obj M).X ◁ N.actLeft)) ≫
          comparisonAux adj A B M N := sorry

/-- The canonical comparison from tensoring a lower shriek to lower-shrieking the tensor after
restriction.  Its underlying map is induced by the balanced-tensor coequalizer. -/
@[stacks 0FRB "relative tensor projection-formula comparison"]
noncomputable def comparisonHom :
    (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).X ⟶
      ((adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N))).X :=
  coequalizer.desc (comparisonAux adj A B M N)
    (comparisonAux_condition adj A B M N)

/-- Precomposing the descended comparison with the ambient balanced-tensor quotient recovers the
unbalanced comparison. -/
@[reassoc]
theorem π_comparisonHom :
    coequalizer.π
        (((adj.rightModuleLowerShriek A).obj M).actRight ▷ N.X)
        ((α_ ((adj.rightModuleLowerShriek A).obj M).X A.X N.X).hom ≫
          (((adj.rightModuleLowerShriek A).obj M).X ◁ N.actLeft)) ≫
      comparisonHom adj A B M N = comparisonAux adj A B M N := sorry

/-- The relative-tensor comparison respects the left action. -/
theorem comparisonHom_left :
    (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).actLeft ≫
        comparisonHom adj A B M N =
      ((Mon.trivial D).X ◁ comparisonHom adj A B M N) ≫
        ((adj.rightModuleLowerShriek B).obj
          (M.tensorBimod ((R.mapBimod A B).obj N))).actLeft := sorry

/-- The relative-tensor comparison respects the right `B`-action. -/
theorem comparisonHom_right :
    (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).actRight ≫
        comparisonHom adj A B M N =
      (comparisonHom adj A B M N ▷ B.X) ≫
        ((adj.rightModuleLowerShriek B).obj
          (M.tensorBimod ((R.mapBimod A B).obj N))).actRight := sorry

/-- The canonical relative-tensor comparison as a morphism of right `B`-modules. -/
@[stacks 0FRB "relative tensor comparison morphism"]
noncomputable def comparison :
    ((adj.rightModuleLowerShriek A).obj M).tensorBimod N ⟶
      (adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N)) where
  hom := comparisonHom adj A B M N
  left_act_hom := comparisonHom_left adj A B M N
  right_act_hom := comparisonHom_right adj A B M N

/-- The carrier map of the module comparison is the coequalizer-induced comparison. -/
@[simp]
theorem comparison_hom :
    (comparison adj A B M N).hom = comparisonHom adj A B M N := sorry

/-- The adjoint-mate map on unbalanced localized tensors underlying the inverse comparison. -/
@[stacks 0FRB "inverse relative tensor comparison on unbalanced tensors"]
noncomputable def inverseAux :
    M.X ⊗ ((R.mapBimod A B).obj N).X ⟶
      R.obj (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).X :=
  adj.projectionFormulaMate M.X N.X ≫
    R.map (coequalizer.π
      (((adj.rightModuleLowerShriek A).obj M).actRight ▷ N.X)
      ((α_ ((adj.rightModuleLowerShriek A).obj M).X A.X N.X).hom ≫
        (((adj.rightModuleLowerShriek A).obj M).X ◁ N.actLeft)))

/-- The adjoint-mate inverse comparison coequalizes the transported `R(A)`-actions. -/
theorem inverseAux_condition :
    (M.actRight ▷ ((R.mapBimod A B).obj N).X) ≫
        inverseAux adj A B M N =
      ((α_ M.X (R.mapMon.obj A).X ((R.mapBimod A B).obj N).X).hom ≫
        (M.X ◁ ((R.mapBimod A B).obj N).actLeft)) ≫
          inverseAux adj A B M N := sorry

/-- The underlying inverse comparison, obtained by descending the projection-formula mate and
then transposing it back across `L ⊣ R`. -/
@[stacks 0FRB "inverse relative tensor projection-formula comparison"]
noncomputable def inverseHom :
    ((adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N))).X ⟶
      (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).X :=
  (adj.homEquiv
    (M.tensorBimod ((R.mapBimod A B).obj N)).X
    (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).X).symm
      (coequalizer.desc (inverseAux adj A B M N)
        (inverseAux_condition adj A B M N))

/-- Transposing the inverse comparison across the ambient adjunction recovers the map descended
from the projection-formula mate. -/
theorem inverseHom_transpose :
    adj.homEquiv
        (M.tensorBimod ((R.mapBimod A B).obj N)).X
        (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).X
        (inverseHom adj A B M N) =
      coequalizer.desc (inverseAux adj A B M N)
        (inverseAux_condition adj A B M N) := sorry

/-- The inverse relative-tensor comparison respects the left action. -/
theorem inverseHom_left :
    ((adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N))).actLeft ≫
        inverseHom adj A B M N =
      ((Mon.trivial D).X ◁ inverseHom adj A B M N) ≫
        (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).actLeft := sorry

/-- The inverse relative-tensor comparison respects the right `B`-action. -/
theorem inverseHom_right :
    ((adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N))).actRight ≫
        inverseHom adj A B M N =
      (inverseHom adj A B M N ▷ B.X) ≫
        (((adj.rightModuleLowerShriek A).obj M).tensorBimod N).actRight := sorry

/-- The inverse relative-tensor comparison as a morphism of right `B`-modules. -/
@[stacks 0FRB "inverse relative tensor comparison morphism"]
noncomputable def inverse :
    (adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N)) ⟶
      ((adj.rightModuleLowerShriek A).obj M).tensorBimod N where
  hom := inverseHom adj A B M N
  left_act_hom := inverseHom_left adj A B M N
  right_act_hom := inverseHom_right adj A B M N

/-- The carrier map of the inverse module comparison is the adjoint-transposed quotient map. -/
@[simp]
theorem inverse_hom :
    (inverse adj A B M N).hom = inverseHom adj A B M N := sorry

/-- The comparison followed by its explicit inverse is the identity. -/
theorem comparison_inverse :
    comparison adj A B M N ≫ inverse adj A B M N = 𝟙 _ := sorry

/-- The explicit inverse followed by the comparison is the identity. -/
theorem inverse_comparison :
    inverse adj A B M N ≫ comparison adj A B M N = 𝟙 _ := sorry

/-- Lemma 24.10.2 (0FRB), generic objectwise form: lower shriek commutes with balanced tensor
against an ambient bimodule, after transporting that bimodule by the monoidal right adjoint. -/
@[stacks 0FRB "relative tensor projection formula"]
noncomputable def iso :
    ((adj.rightModuleLowerShriek A).obj M).tensorBimod N ≅
      (adj.rightModuleLowerShriek B).obj
        (M.tensorBimod ((R.mapBimod A B).obj N)) where
  hom := comparison adj A B M N
  inv := inverse adj A B M N
  hom_inv_id := comparison_inverse adj A B M N
  inv_hom_id := inverse_comparison adj A B M N

/-- The forward morphism of the relative-tensor isomorphism is the canonical comparison. -/
@[simp]
theorem iso_hom : (iso adj A B M N).hom = comparison adj A B M N := sorry

/-- The inverse morphism of the relative-tensor isomorphism is the adjoint-transposed comparison. -/
@[simp]
theorem iso_inv : (iso adj A B M N).inv = inverse adj A B M N := sorry

end Comparison

section Source

variable [HasCoequalizers D]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The components defining `sourceMap` are natural in the ambient bimodule. -/
theorem sourceMap_naturality (A B : Mon D)
    {M M' : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ M')
    {N N' : Bimod A B} (g : N ⟶ N') :
    (Bimod.tensorLeft (T := B) ((adj.rightModuleLowerShriek A).obj M)).map g ≫
        Bimod.whiskerRight ((adj.rightModuleLowerShriek A).map f) N' =
      Bimod.whiskerRight ((adj.rightModuleLowerShriek A).map f) N ≫
        (Bimod.tensorLeft (T := B) ((adj.rightModuleLowerShriek A).obj M')).map g := sorry

/-- The left side of the relative-tensor projection formula, functorial in the localized right
module and the ambient bimodule, on a morphism of localized modules. -/
noncomputable def sourceMap (A B : Mon D)
    {M M' : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ M') :
    Bimod.tensorLeft (T := B) ((adj.rightModuleLowerShriek A).obj M) ⟶
      Bimod.tensorLeft (T := B) ((adj.rightModuleLowerShriek A).obj M') where
  app N := Bimod.whiskerRight ((adj.rightModuleLowerShriek A).map f) N
  naturality := fun {X Y} g ↦
    sourceMap_naturality adj A B f (N := X) (N' := Y) g

/-- The source-side map is the identity on an identity module morphism. -/
theorem sourceMap_id (A B : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) :
    sourceMap adj A B (𝟙 M) = 𝟙 _ := sorry

/-- The source-side maps preserve composition of localized module morphisms. -/
theorem sourceMap_comp (A B : Mon D)
    {M M' M'' : Bimod.RightModule (R.mapMon.obj A)}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    sourceMap adj A B (f ≫ g) = sourceMap adj A B f ≫ sourceMap adj A B g := sorry

/-- The left side of the relative-tensor projection formula, functorial in the localized right
module and the ambient bimodule. -/
@[stacks 0FRB "lower shriek followed by relative tensor"]
noncomputable def sourceFunctor (A B : Mon D) :
    Bimod.RightModule (R.mapMon.obj A) ⥤ Bimod A B ⥤ Bimod.RightModule B where
  obj M := Bimod.tensorLeft ((adj.rightModuleLowerShriek A).obj M)
  map f := sourceMap adj A B f
  map_id M := sourceMap_id adj A B M
  map_comp f g := sourceMap_comp adj A B f g

end Source

section Target

variable [HasCoequalizers C]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The components defining `targetMap` are natural in the ambient bimodule. -/
theorem targetMap_naturality (A B : Mon D)
    {M M' : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ M')
    {N N' : Bimod A B} (g : N ⟶ N') :
    (R.mapBimod A B ⋙ Bimod.tensorLeft M ⋙
        adj.rightModuleLowerShriek B).map g ≫
        (adj.rightModuleLowerShriek B).map
          (Bimod.whiskerRight f ((R.mapBimod A B).obj N')) =
      (adj.rightModuleLowerShriek B).map
          (Bimod.whiskerRight f ((R.mapBimod A B).obj N)) ≫
        (R.mapBimod A B ⋙ Bimod.tensorLeft M' ⋙
          adj.rightModuleLowerShriek B).map g := sorry

/-- The right side of the relative-tensor projection formula on a morphism of localized right
modules. -/
noncomputable def targetMap (A B : Mon D)
    {M M' : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ M') :
    R.mapBimod A B ⋙ Bimod.tensorLeft M ⋙ adj.rightModuleLowerShriek B ⟶
      R.mapBimod A B ⋙ Bimod.tensorLeft M' ⋙ adj.rightModuleLowerShriek B where
  app N := (adj.rightModuleLowerShriek B).map
    (Bimod.whiskerRight f ((R.mapBimod A B).obj N))
  naturality := fun {X Y} g ↦
    targetMap_naturality adj A B f (N := X) (N' := Y) g

/-- The target-side map is the identity on an identity module morphism. -/
theorem targetMap_id (A B : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) :
    targetMap adj A B (𝟙 M) = 𝟙 _ := sorry

/-- The target-side maps preserve composition of localized module morphisms. -/
theorem targetMap_comp (A B : Mon D)
    {M M' M'' : Bimod.RightModule (R.mapMon.obj A)}
    (f : M ⟶ M') (g : M' ⟶ M'') :
    targetMap adj A B (f ≫ g) = targetMap adj A B f ≫ targetMap adj A B g := sorry

/-- The right side of the relative-tensor projection formula, functorial in the localized right
module and the ambient bimodule. -/
@[stacks 0FRB "relative tensor after restriction followed by lower shriek"]
noncomputable def targetFunctor (A B : Mon D) :
    Bimod.RightModule (R.mapMon.obj A) ⥤ Bimod A B ⥤ Bimod.RightModule B where
  obj M := R.mapBimod A B ⋙ Bimod.tensorLeft M ⋙ adj.rightModuleLowerShriek B
  map f := targetMap adj A B f
  map_id M := targetMap_id adj A B M
  map_comp f g := targetMap_comp adj A B f g

end Target

section Naturality

variable [HasCoequalizers C] [HasCoequalizers D]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
variable [∀ X : D, PreservesColimitsOfSize.{0, 0} (tensorRight X)]

/-- The objectwise relative-tensor isomorphism is natural in the ambient bimodule. -/
theorem iso_natural_right (A B : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) {N N' : Bimod A B} (g : N ⟶ N') :
    ((sourceFunctor adj A B).obj M).map g ≫ (iso adj A B M N').hom =
      (iso adj A B M N).hom ≫ ((targetFunctor adj A B).obj M).map g := sorry

/-- The relative-tensor projection formula as a natural isomorphism in the ambient bimodule. -/
@[stacks 0FRB "relative tensor projection formula natural in the bimodule"]
noncomputable def isoRight (A B : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) :
    (sourceFunctor adj A B).obj M ≅ (targetFunctor adj A B).obj M :=
  NatIso.ofComponents (fun N ↦ iso adj A B M N) (iso_natural_right adj A B M)

/-- The one-variable natural isomorphisms are natural in the localized right module. -/
theorem iso_natural_left (A B : Mon D)
    {M M' : Bimod.RightModule (R.mapMon.obj A)} (f : M ⟶ M') :
    (sourceFunctor adj A B).map f ≫ (isoRight adj A B M').hom =
      (isoRight adj A B M).hom ≫ (targetFunctor adj A B).map f := sorry

/-- Lemma 24.10.2 (0FRB), reusable form: the relative-tensor projection formula as an
isomorphism of curried bifunctors, hence functorial in both the module and bimodule variables. -/
@[stacks 0FRB "relative tensor projection formula natural in both variables"]
noncomputable def natIso (A B : Mon D) :
    sourceFunctor adj A B ≅ targetFunctor adj A B :=
  NatIso.ofComponents (isoRight adj A B) (iso_natural_left adj A B)

/-- The component of the bifunctorial projection formula is the explicitly constructed
objectwise relative-tensor isomorphism. -/
@[simp]
theorem natIso_app_app (A B : Mon D)
    (M : Bimod.RightModule (R.mapMon.obj A)) (N : Bimod A B) :
    ((natIso adj A B).app M).app N = iso adj A B M N := sorry

end Naturality

end RelativeTensor

end CategoryTheory.Adjunction

end
