/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Category.Cat
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Order.WithBot
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X]

/-- The open of `X` underlying an open neighborhood of the support of `I`. -/
abbrev openNhdsAsOpen (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) : X.Opens :=
  V.val

/-- The open subscheme of an open neighborhood of the support of `I`. -/
abbrev openNhdsScheme (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) : Scheme.{u} :=
  (openNhdsAsOpen I V).toScheme

/-- The open immersion of an open neighborhood of the support of `I`. -/
abbrev openNhdsι (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    openNhdsScheme I V ⟶ X :=
  (openNhdsAsOpen I V).ι

/-- The open subscheme of a neighborhood is the canonical open restriction of its underlying open. -/
theorem openNhdsScheme_eq (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    openNhdsScheme I V = (openNhdsAsOpen I V).toScheme := sorry

/-- The image of the closed subscheme cut out by `I` is contained in every open neighborhood of
the support of `I`. -/
theorem range_subschemeι_subset_openNhds (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    Set.range I.subschemeι ⊆ Set.range (openNhdsι I V) := sorry

/-- The closed-immersion factorization `Y ⟶ V` of `I.subschemeι` through an open neighborhood
`V` of the support of `I`. -/
def closedSubschemeιOnOpen (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    I.subscheme ⟶ openNhdsScheme I V :=
  IsOpenImmersion.lift (openNhdsι I V) I.subschemeι (range_subschemeι_subset_openNhds I V)

/-- The factorization `Y ⟶ V` composes to the closed immersion of `Y` in `X`. -/
theorem closedSubschemeιOnOpen_comp (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    closedSubschemeιOnOpen I V ≫ openNhdsι I V = I.subschemeι := sorry

namespace FiniteEtaleNeighborhood

/-- Open neighborhoods of the support, ordered by inclusion, with the closed subscheme as
an additional bottom index. -/
abbrev Index (I : X.IdealSheafData) :=
  WithBot (CoherentCompletion.compactSupport I).openNhds

/-- The scheme diagram consisting of the closed subscheme and its open neighborhoods,
with their geometric inclusions. -/
def base (I : X.IdealSheafData) : Index I ⥤ Scheme.{u} :=
  let object : Index I → Scheme.{u} := fun index =>
    match index with
    | none => I.subscheme
    | some neighborhood => openNhdsScheme I neighborhood
  let arrow : ∀ {source target : Index I}, (source ⟶ target) →
      (object source ⟶ object target) := fun {source target} inclusion =>
    match source, target, leOfHom inclusion with
    | none, none, _ => 𝟙 I.subscheme
    | none, some neighborhood, _ => closedSubschemeιOnOpen I neighborhood
    | some smaller, some larger, containment =>
        X.homOfLE (WithBot.coe_le_coe.mp containment : smaller ≤ larger)
    | some neighborhood, none, containment =>
        False.elim (WithBot.not_coe_le_bot neighborhood containment)
  let laws : (∀ index, arrow (𝟙 index) = 𝟙 (object index)) ∧
      (∀ {first second third : Index I} (left : first ⟶ second) (right : second ⟶ third),
        arrow (left ≫ right) = arrow left ≫ arrow right) := sorry
  { obj := object
    map := arrow
    map_id := laws.1
    map_comp := laws.2 }

/-- The geometric base diagram on all indices contained in an open neighborhood. -/
def systemBase (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    {index : Index I // index ≤ (V : Index I)} ⥤ Scheme.{u} :=
  (OrderHom.Subtype.val (fun index : Index I => index ≤ (V : Index I))).toFunctor ⋙ base I

/-- A system over a neighborhood is cartesian when its component maps are finite étale
and all its transition squares are pullbacks. -/
def IsCartesian (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    ObjectProperty (Over (systemBase I V)) := fun system =>
  (∀ index, finiteEtaleMorphism (system.hom.app index)) ∧
    (∀ {source target} (inclusion : source ⟶ target),
      IsPullback (system.left.map inclusion) (system.hom.app source)
        (system.hom.app target) ((systemBase I V).map inclusion))

/-- The category of cartesian finite étale systems on the indices below a neighborhood. -/
abbrev System (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :=
  (IsCartesian I V).FullSubcategory

/-- Restriction of a cartesian finite étale system to a smaller neighborhood. -/
def restrict (I : X.IdealSheafData)
    {V W : (CoherentCompletion.compactSupport I).openNhds} (containment : W ≤ V) :
    System I V ⥤ System I W :=
  let inclusion : {index : Index I // index ≤ (W : Index I)} ⥤
      {index : Index I // index ≤ (V : Index I)} :=
    (⟨fun index => ⟨index.val, index.property.trans (WithBot.coe_le_coe.mpr containment)⟩,
      fun _ _ inequality => inequality⟩ : OrderHom _ _).toFunctor
  let raw : System I V ⥤ Over (systemBase I W) :=
    (IsCartesian I V).ι ⋙
      Over.post ((Functor.whiskeringLeft _ _ Scheme.{u}).obj inclusion)
  let cartesian : ∀ system, IsCartesian I W (raw.obj system) := sorry
  (IsCartesian I W).lift raw cartesian

/-- Evaluation of a cartesian finite étale system at any index below its neighborhood. -/
def eval (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds)
    (index : {index : Index I // index ≤ (V : Index I)}) :
    System I V ⥤ FiniteEtale ((base I).obj index.val) :=
  let raw := (IsCartesian I V).ι ⋙
    Over.post ((CategoryTheory.evaluation _ Scheme.{u}).obj index)
  let finiteEtale : ∀ system, finiteEtaleMorphism (raw.obj system).hom := sorry
  MorphismProperty.Comma.lift raw finiteEtale (fun _ => trivial) (fun _ => trivial)

/-- A finite étale cover determines a cartesian system by pullback to every index below
its base neighborhood. -/
def ofCover (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    FiniteEtale (openNhdsScheme I V) ⥤ System I V :=
  let top : {index : Index I // index ≤ (V : Index I)} := ⟨V, le_rfl⟩
  let toTop := fun index : {index : Index I // index ≤ (V : Index I)} =>
    (systemBase I V).map (homOfLE index.property : index ⟶ top)
  let diagram := fun cover : FiniteEtale (openNhdsScheme I V) =>
    ({ obj := fun index => pullback cover.hom (toTop index)
       map := fun {source target} inclusion =>
         pullback.lift (pullback.fst cover.hom (toTop source))
           (pullback.snd cover.hom (toTop source) ≫ (systemBase I V).map inclusion) sorry
       map_id := sorry
       map_comp := sorry } :
      {index : Index I // index ≤ (V : Index I)} ⥤ Scheme.{u})
  let projection := fun cover : FiniteEtale (openNhdsScheme I V) =>
    ({ app := fun index => pullback.snd cover.hom (toTop index)
       naturality := sorry } : diagram cover ⟶ systemBase I V)
  let raw : FiniteEtale (openNhdsScheme I V) ⥤ Over (systemBase I V) :=
    { obj := fun cover => Over.mk (projection cover)
      map := fun {source target} coverMap =>
        Over.homMk
          { app := fun index =>
              pullback.lift (pullback.fst source.hom (toTop index) ≫ coverMap.left)
                (pullback.snd source.hom (toTop index)) sorry
            naturality := sorry } sorry
      map_id := sorry
      map_comp := sorry }
  let cartesian : ∀ cover, IsCartesian I V (raw.obj cover) := sorry
  (IsCartesian I V).lift raw cartesian

/-- Evaluation at the top neighborhood is equivalent to its category of finite étale covers,
with inverse given by the system of pullbacks. -/
def evalEquivalence (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    System I V ≌ FiniteEtale (openNhdsScheme I V) :=
  let top : {index : Index I // index ≤ (V : Index I)} := ⟨V, le_rfl⟩
  let forward := eval I V top
  let inverse := ofCover I V
  let comparison : ∀ system : System I V,
      system.obj.left ≅ (inverse.obj (forward.obj system)).obj.left := fun system =>
    NatIso.ofComponents
      (fun index => (system.property.2 (homOfLE index.property : index ⟶ top)).isoPullback) sorry
  let unitComponent := fun system : System I V =>
    ObjectProperty.isoMk (IsCartesian I V)
      (Over.isoMk (comparison system) sorry : system.obj ≅ (inverse.obj (forward.obj system)).obj)
  let unit : 𝟭 (System I V) ≅ forward ⋙ inverse :=
    NatIso.ofComponents unitComponent sorry
  let counitComponent := fun cover : FiniteEtale (openNhdsScheme I V) =>
    MorphismProperty.Over.isoMk
      ({ hom := pullback.fst cover.hom ((systemBase I V).map (𝟙 top))
         inv := pullback.lift (𝟙 cover.left) cover.hom sorry
         hom_inv_id := sorry
         inv_hom_id := sorry } : (forward.obj (inverse.obj cover)).left ≅ cover.left) sorry
  let counit : inverse ⋙ forward ≅ 𝟭 (FiniteEtale (openNhdsScheme I V)) :=
    NatIso.ofComponents counitComponent sorry
  CategoryTheory.Equivalence.mk forward inverse unit counit

/-- Evaluation at any index is naturally isomorphic to top evaluation followed by geometric
base change along the corresponding inclusion. -/
def evalBaseChangeIso (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds)
    (index : {index : Index I // index ≤ (V : Index I)}) :
    eval I V index ≅ eval I V ⟨V, le_rfl⟩ ⋙
      finiteEtaleBaseChange ((systemBase I V).map
        (homOfLE index.property : index ⟶ ⟨V, le_rfl⟩)) :=
  NatIso.ofComponents (fun system =>
    let square := system.property.2 (homOfLE index.property : index ⟶ ⟨V, le_rfl⟩)
    MorphismProperty.Over.isoMk square.isoPullback square.isoPullback_hom_snd) sorry

end FiniteEtaleNeighborhood

/-- The diagram of finite étale categories on open neighborhoods of the closed support of `I`,
indexed by reverse inclusion. -/
def finiteEtaleNeighborhoodDiagram (I : X.IdealSheafData) :
    (CoherentCompletion.compactSupport I).openNhdsᵒᵖ ⥤ Cat :=
  let object := fun V : (CoherentCompletion.compactSupport I).openNhdsᵒᵖ =>
    Cat.of (FiniteEtaleNeighborhood.System I V.unop)
  let arrow := fun {V W : (CoherentCompletion.compactSupport I).openNhdsᵒᵖ} (a : V ⟶ W) =>
    (FiniteEtaleNeighborhood.restrict I (leOfHom a.unop)).toCatHom
  let laws : (∀ V, arrow (𝟙 V) = 𝟙 (object V)) ∧
      (∀ {U V W} (left : U ⟶ V) (right : V ⟶ W),
        arrow (left ≫ right) = arrow left ≫ arrow right) := sorry
  { obj := object
    map := arrow
    map_id := laws.1
    map_comp := laws.2 }

/-- At an open neighborhood, the finite étale neighborhood diagram is the category of
cartesian finite étale systems below that neighborhood. -/
theorem finiteEtaleNeighborhoodDiagram_obj (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    (finiteEtaleNeighborhoodDiagram I).obj (op V) =
      Cat.of (FiniteEtaleNeighborhood.System I V) := sorry

/-- Restriction of finite étale schemes from open neighborhoods of `Y` to the closed subscheme
`Y = I.subscheme`. -/
def finiteEtaleNeighborhoodRestrictionCocone (I : X.IdealSheafData) :
    Cocone (finiteEtaleNeighborhoodDiagram I) where
  pt := Cat.of (FiniteEtale I.subscheme)
  ι :=
    { app := fun V =>
        (FiniteEtaleNeighborhood.eval I V.unop ⟨⊥, bot_le⟩).toCatHom
      naturality := sorry }

/-- The component of the neighborhood restriction cocone is evaluation at the closed
subscheme index. -/
theorem finiteEtaleNeighborhoodRestrictionCocone_ι (I : X.IdealSheafData)
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    (finiteEtaleNeighborhoodRestrictionCocone I).ι.app (op V) =
      (FiniteEtaleNeighborhood.eval I V ⟨⊥, bot_le⟩).toCatHom := sorry

/-- The functor `colim_V FÉt_V ⟶ FÉt_Y` induced by a chosen colimit cocone of the neighborhood
finite étale diagram. -/
def finiteEtaleNeighborhoodRestriction (I : X.IdealSheafData)
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    t.cocone.pt ⥤ Cat.of (FiniteEtale I.subscheme) :=
  (t.isColimit.desc (finiteEtaleNeighborhoodRestrictionCocone I)).toFunctor

/-- Restriction out of a colimit cocone recovers base change along `Y ⟶ V` on each neighborhood. -/
theorem finiteEtaleNeighborhoodRestriction_fac (I : X.IdealSheafData)
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I))
    (V : (CoherentCompletion.compactSupport I).openNhds) :
    t.cocone.ι.app (op V) ≫ (finiteEtaleNeighborhoodRestriction I t).toCatHom =
      (finiteEtaleNeighborhoodRestrictionCocone I).ι.app (op V) := sorry

/-- Full faithfulness of neighborhood completion on finite locally free objects implies full
faithfulness of restriction from the colimit of finite étale neighborhood categories to the
closed subscheme. -/
theorem finiteEtaleNeighborhoodRestriction_fullyFaithful_of_completion
    {X : Scheme.{u}} [IsNoetherian X] (I : X.IdealSheafData)
    (h_completion : CoherentCompletion.NeighborhoodCompletionFullyFaithful I)
    (t : ColimitCocone (finiteEtaleNeighborhoodDiagram I)) :
    Nonempty (finiteEtaleNeighborhoodRestriction I t).FullyFaithful := sorry

end AlgebraicGeometry.Scheme
