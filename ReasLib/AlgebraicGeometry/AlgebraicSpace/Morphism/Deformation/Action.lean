/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Perturbation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Deformation.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Conormal.BaseChange

/-!
# Hom-sheaf action on infinitesimal deformations of maps of algebraic spaces

After identifying sheaves on `X` and `X'` via the spaces-étale equivalence of a
thickening, local `𝒪`-linear maps `(a|_U)^* Ω_{Y/B} ⟶ C_{U/U'}` act on compatible
lifts of `a` by their uniquely specified first-order perturbations. The action
is simply transitive on any spaces-étale object that carries a lift.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Hom.Deformation

variable {S : Scheme.{u}} {B X X' Y Y' : AlgebraicSpace S}

/-- Base change of a first-order thickening along an étale map of algebraic spaces
remains a first-order thickening. -/
instance closedι_isFirstOrderThickening (iX : X ⟶ X') (U' : spacesEtaleSite X')
    [IsFirstOrderThickening iX] : IsFirstOrderThickening (closedι iX U') :=
  sorry

/-- The type of `𝒪_U`-linear maps `(a|_U)^* Ω_{Y/B} ⟶ C_{U/U'}`, evaluating the
Hom sheaf of `X` on `U = X ×_{X'} U'`. -/
abbrev parameterHom (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :=
  (Modules.pullback (toSource iX U' ≫ a)).obj (relativeDifferentials (iY ≫ sY')) ⟶
    conormalSheaf (closedι iX U')

/-- Restriction of a local Hom parameter along a morphism of spaces-étale objects. -/
def restrictParameter (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'} (f : V' ⟶ U')
    (θ : parameterHom sY' iX iY a U') : parameterHom sY' iX iY a V' :=
  let g := (spacesEtalePullback iX).map f
  eqToHom (congrArg
      (fun t ↦ (Modules.pullback t).obj (relativeDifferentials (iY ≫ sY')))
      (by
        rw [← Category.assoc]
        exact congrArg (fun t ↦ t ≫ a)
          (g.w.trans (Category.comp_id (toSource iX V'))).symm)) ≫
    (Modules.pullbackCompIso g.left (toSource iX U' ≫ a)).inv.app _ ≫
      (Modules.pullback g.left).map θ ≫
        Conormal.map (⟨by exact pullback.lift_fst _ _ _⟩ :
          CommSq g.left (closedι iX V') (closedι iX U') f.left)

/-- Restriction along the identity leaves a local Hom parameter unchanged. -/
theorem restrictParameter_id (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] (U' : spacesEtaleSite X')
    (θ : parameterHom sY' iX iY a U') :
    restrictParameter sY' iX iY a (𝟙 U') θ = θ :=
  sorry

/-- Successive restrictions of local Hom parameters equal restriction along the composite. -/
theorem restrictParameter_comp (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' W' : spacesEtaleSite X'}
    (f : W' ⟶ V') (g : V' ⟶ U') (θ : parameterHom sY' iX iY a U') :
    restrictParameter sY' iX iY a f (restrictParameter sY' iX iY a g θ) =
      restrictParameter sY' iX iY a (f ≫ g) θ :=
  sorry

/-- Restriction of the zero local Hom parameter is zero. -/
theorem restrictParameter_zero (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') :
    restrictParameter sY' iX iY a f 0 = 0 :=
  sorry

/-- Restriction of local Hom parameters preserves addition. -/
theorem restrictParameter_add (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') (θ η : parameterHom sY' iX iY a U') :
    restrictParameter sY' iX iY a f (θ + η) =
      restrictParameter sY' iX iY a f θ + restrictParameter sY' iX iY a f η :=
  sorry

/-- Canonical conormal base change identifies morphisms between the restrictions
of `a^* Ω_{Y/B}` and `C_{X/X'}` with local Hom parameters. -/
theorem parameterHom_baseChange_bijective (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX]
    (U' : spacesEtaleSite X') :
    Function.Bijective (fun θ :
      (Modules.pullback (toSource iX U')).obj
          ((Modules.pullback a).obj (relativeDifferentials (iY ≫ sY'))) ⟶
        (Modules.pullback (toSource iX U')).obj (conormalSheaf iX) ↦
      ((Modules.pullbackCompIso (toSource iX U') a).inv.app _ ≫ θ ≫
        Conormal.map (thickeningPullbackSq iX U') : parameterHom sY' iX iY a U')) :=
  sorry

/-- The presheaf on `X'_spaces,étale` whose value at `U'` is the type of
`𝒪_U`-linear maps `(a|_U)^* Ω_{Y/B} ⟶ C_{U/U'}`. -/
noncomputable def parameterPresheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    (spacesEtaleSite X')ᵒᵖ ⥤ Type (u + 1) where
  obj U' := parameterHom sY' iX iY a U'.unop
  map f := TypeCat.ofHom fun θ ↦ restrictParameter sY' iX iY a f.unop θ
  map_id U' :=
    congrArg TypeCat.ofHom (funext (restrictParameter_id sY' iX iY a U'.unop))
  map_comp f g :=
    congrArg TypeCat.ofHom (funext fun θ ↦
      (restrictParameter_comp sY' iX iY a g.unop f.unop θ).symm)

/-- Evaluating `parameterPresheaf` recovers the local Hom type on
`U = X ×_{X'} U'`. -/
theorem parameterPresheaf_obj (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    (parameterPresheaf sY' iX iY a).obj (op U') = parameterHom sY' iX iY a U' :=
  by rfl

/-- The restriction maps of `parameterPresheaf` are `restrictParameter`. -/
theorem parameterPresheaf_map (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') (θ : (parameterPresheaf sY' iX iY a).obj (op U')) :
    (parameterPresheaf sY' iX iY a).map f.op θ =
      restrictParameter sY' iX iY a f θ :=
  TypeCat.ofHom_apply (fun η ↦ restrictParameter sY' iX iY a f η) θ

/-- Local Hom parameters form a sheaf of types on `X'_spaces,étale`. -/
theorem parameterSheaf_isSheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    Presheaf.IsSheaf (spacesEtaleTopology X') (parameterPresheaf sY' iX iY a) :=
  sorry

/-- The sheaf of infinitesimal Hom parameters on the spaces-étale site of `X'`,
identified with `Hom_{𝒪_X}(a^* Ω_{Y/B}, C_{X/X'})` via the étale-site equivalence of the thickening. -/
noncomputable def parameterSheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    Sheaf (spacesEtaleTopology X') (Type (u + 1)) :=
  ⟨parameterPresheaf sY' iX iY a, parameterSheaf_isSheaf sY' iX iY a⟩

/-- Evaluating `parameterSheaf` recovers the local Hom type on
`U = X ×_{X'} U'`. -/
theorem parameterSheaf_obj (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    (parameterSheaf sY' iX iY a).obj.obj (op U') = parameterHom sY' iX iY a U' :=
  by rfl

/-- The restriction maps of `parameterSheaf` are `restrictParameter`. -/
theorem parameterSheaf_map (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') (θ : (parameterSheaf sY' iX iY a).obj.obj (op U')) :
    (parameterSheaf sY' iX iY a).obj.map f.op θ =
      restrictParameter sY' iX iY a f θ :=
  TypeCat.ofHom_apply (fun η ↦ restrictParameter sY' iX iY a f η) θ

/-- A compatible lift `t` is the first-order perturbation of a compatible lift
`s` prescribed by a local Hom parameter `θ`. -/
def IsSectionPerturbation (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX]
    [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (θ : parameterHom sY' iX iY a U')
    (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) : Prop :=
  ∃ sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY s.1,
    @IsPerturbation S B (closedSpace iX U') U'.left Y Y' (iY ≫ sY')
      (U'.hom ≫ sX') sY' (closedι iX U') iY (toSource iX U' ≫ a) s.1
      (closedι_isFirstOrderThickening iX U') ‹IsFirstOrderThickening iY› sq θ t.1

/-- `IsSectionPerturbation` is the localization of `IsPerturbation` to
`U ⊂ U'`. -/
theorem isSectionPerturbation_iff (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX]
    [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (θ : parameterHom sY' iX iY a U')
    (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) :
    IsSectionPerturbation sX' sY' iX iY a A U' θ s t ↔
      ∃ sq : CommSq (toSource iX U' ≫ a) (closedι iX U') iY s.1,
        @IsPerturbation S B (closedSpace iX U') U'.left Y Y' (iY ≫ sY')
          (U'.hom ≫ sX') sY' (closedι iX U') iY (toSource iX U' ≫ a) s.1
          (closedι_isFirstOrderThickening iX U') ‹IsFirstOrderThickening iY›
          sq θ t.1 :=
  Iff.rfl

/-- The sheaf of Hom parameters acts on the sheaf of compatible lifts: each local
parameter uniquely perturbs a given compatible section. -/
theorem existsUnique_sectionPerturbation (sX' : X' ⟶ B) (sY' : Y' ⟶ B)
    (iX : X ⟶ X') (iY : Y ⟶ Y') (a : X ⟶ Y)
    [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (θ : parameterHom sY' iX iY a U')
    (s : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) :
    ExistsUnique fun t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U') ↦
      IsSectionPerturbation sX' sY' iX iY a A U' θ s t :=
  sorry

/-- The zero Hom parameter acts as the identity on a compatible lift. -/
theorem act_zero (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X')
    (s : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) :
    IsSectionPerturbation sX' sY' iX iY a A U' 0 s s :=
  sorry

/-- Acting by a sum of Hom parameters is successive action. -/
theorem act_add (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X') (θ η : parameterHom sY' iX iY a U')
    (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) :
    IsSectionPerturbation sX' sY' iX iY a A U' (θ + η) s t ↔
      ∃ u : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U'),
        IsSectionPerturbation sX' sY' iX iY a A U' η s u ∧
          IsSectionPerturbation sX' sY' iX iY a A U' θ u t :=
  sorry

/-- Restriction of compatible lifts is equivariant for restriction of Hom
parameters. -/
theorem act_naturality (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U')
    (θ : parameterHom sY' iX iY a U')
    (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U'))
    (h : IsSectionPerturbation sX' sY' iX iY a A U' θ s t) :
    IsSectionPerturbation sX' sY' iX iY a A V'
      (restrictParameter sY' iX iY a f θ)
      ((sectionsPresheaf sX' sY' iX iY a A).map f.op s)
      ((sectionsPresheaf sX' sY' iX iY a A).map f.op t) :=
  sorry

/-- Given one compatible lift on `U'`, translation by Hom parameters is simply
transitive on the set of compatible lifts. -/
theorem act_simplyTransitive (sX' : X' ⟶ B) (sY' : Y' ⟶ B) (iX : X ⟶ X')
    (iY : Y ⟶ Y') (a : X ⟶ Y) [IsFirstOrderThickening iX]
    [IsFirstOrderThickening iY]
    (A : (Modules.pullback a).obj (conormalSheaf iY) ⟶ conormalSheaf iX)
    (U' : spacesEtaleSite X')
    (s t : (sectionsSheaf sX' sY' iX iY a A).obj.obj (op U')) :
    ExistsUnique fun θ : parameterHom sY' iX iY a U' ↦
      IsSectionPerturbation sX' sY' iX iY a A U' θ s t :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom.Deformation
