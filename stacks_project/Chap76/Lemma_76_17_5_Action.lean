/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_17_2_Perturbation
public import stacks_project.Chap76.Lemma_76_17_4_Sheaf

/-!
# Hom-sheaf action on infinitesimal deformations of maps of algebraic spaces

After identifying sheaves on `X` and `X'` via the spaces-étale equivalence of a
thickening, local `𝒪`-linear maps `(a|_U)^* Ω_{Y/B} ⟶ C_{U/U'}` act on compatible
lifts of `a` by the unique first-order perturbation of Lemma 76.17.2. The action
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

/-- The fibre-product identity used to lift a spaces-étale restriction to closed
subspaces. -/
def closedMap_condition (iX : X ⟶ X') {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') :
    (closedι iX V' ≫ f.left) ≫ U'.hom = toSource iX V' ≫ iX :=
  ((Category.assoc (closedι iX V') f.left U'.hom).trans
      (congrArg (fun t ↦ closedι iX V' ≫ t)
        (f.w.trans (Category.comp_id V'.hom)))).trans
    (pullback.condition :
      pullback.fst V'.hom iX ≫ V'.hom = pullback.snd V'.hom iX ≫ iX)

/-- The morphism `X ×_{X'} V' ⟶ X ×_{X'} U'` induced by a spaces-étale map
`V' ⟶ U'`. -/
def closedMap (iX : X ⟶ X') {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') :
    closedSpace iX V' ⟶ closedSpace iX U' :=
  pullback.lift (closedι iX V' ≫ f.left) (toSource iX V') (closedMap_condition iX f)

/-- The commutative square of first-order thickenings induced by a spaces-étale
restriction. -/
def closedMapSq (iX : X ⟶ X') {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') :
    CommSq (closedMap iX f) (closedι iX V') (closedι iX U') f.left :=
  ⟨pullback.lift_fst (closedι iX V' ≫ f.left) (toSource iX V') (closedMap_condition iX f)⟩

/-- Pullback of the structure map `U ⟶ X` along a spaces-étale restriction. -/
def closedMap_comp_toSource (iX : X ⟶ X') {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') : closedMap iX f ≫ toSource iX U' = toSource iX V' :=
  pullback.lift_snd (closedι iX V' ≫ f.left) (toSource iX V') (closedMap_condition iX f)

/-- Compatibility of `closedMap` with postcomposition by `a : X ⟶ Y`. -/
def closedMap_comp_toSource_comp (iX : X ⟶ X') (a : X ⟶ Y)
    {U' V' : spacesEtaleSite X'} (f : V' ⟶ U') :
    closedMap iX f ≫ toSource iX U' ≫ a = toSource iX V' ≫ a :=
  (Category.assoc (closedMap iX f) (toSource iX U') a).symm.trans
    (congrArg (fun t ↦ t ≫ a) (closedMap_comp_toSource iX f))

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
  eqToHom (congrArg
      (fun t ↦ (Modules.pullback t).obj (relativeDifferentials (iY ≫ sY')))
      (closedMap_comp_toSource_comp iX a f).symm) ≫
    (Modules.pullbackComp (closedMap iX f) (toSource iX U' ≫ a)).inv.app _ ≫
      (Modules.pullback (closedMap iX f)).map θ ≫ Conormal.map (closedMapSq iX f)

/-- The presheaf on `X'_spaces,étale` whose value at `U'` is the type of
`𝒪_U`-linear maps `(a|_U)^* Ω_{Y/B} ⟶ C_{U/U'}`. -/
noncomputable def parameterPresheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    (spacesEtaleSite X')ᵒᵖ ⥤ Type (u + 1) where
  obj U' := parameterHom sY' iX iY a U'.unop
  map {U' V'} f := TypeCat.ofHom fun θ ↦ restrictParameter sY' iX iY a f.unop θ
  map_id := sorry
  map_comp := sorry

/-- Evaluating `parameterPresheaf` recovers the local Hom type on
`U = X ×_{X'} U'`. -/
theorem parameterPresheaf_obj (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    (parameterPresheaf sY' iX iY a).obj (op U') = parameterHom sY' iX iY a U' :=
  sorry

/-- The restriction maps of `parameterPresheaf` are `restrictParameter`. -/
theorem parameterPresheaf_map (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') (θ : (parameterPresheaf sY' iX iY a).obj (op U')) :
    (parameterPresheaf sY' iX iY a).map f.op θ =
      restrictParameter sY' iX iY a f θ :=
  sorry

/-- Local Hom parameters form a sheaf of types on `X'_spaces,étale`. -/
theorem parameterSheaf_isSheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    Presheaf.IsSheaf (spacesEtaleTopology X') (parameterPresheaf sY' iX iY a) :=
  sorry

/-- The sheaf of infinitesimal Hom parameters on the spaces-étale site of `X'`,
identified with `Hom_{𝒪_X}(a^* Ω_{Y/B}, C_{X/X'})` via 76.9.1.1. -/
noncomputable def parameterSheaf (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] :
    Sheaf (spacesEtaleTopology X') (Type (u + 1)) :=
  ⟨parameterPresheaf sY' iX iY a, parameterSheaf_isSheaf sY' iX iY a⟩

/-- Evaluating `parameterSheaf` recovers the local Hom type on
`U = X ×_{X'} U'`. -/
theorem parameterSheaf_obj (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] (U' : spacesEtaleSite X') :
    (parameterSheaf sY' iX iY a).obj.obj (op U') = parameterHom sY' iX iY a U' :=
  sorry

/-- The restriction maps of `parameterSheaf` are `restrictParameter`. -/
theorem parameterSheaf_map (sY' : Y' ⟶ B) (iX : X ⟶ X') (iY : Y ⟶ Y')
    (a : X ⟶ Y) [IsFirstOrderThickening iX] {U' V' : spacesEtaleSite X'}
    (f : V' ⟶ U') (θ : (parameterSheaf sY' iX iY a).obj.obj (op U')) :
    (parameterSheaf sY' iX iY a).obj.map f.op θ =
      restrictParameter sY' iX iY a f θ :=
  sorry

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
  sorry

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
