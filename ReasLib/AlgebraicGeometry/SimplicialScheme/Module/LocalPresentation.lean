/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.QCoh.Basic
public import ReasLib.Topology.Category.TopCat.DiagramOpens.Component
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous.Colimits
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.ConcreteSheafification
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Local presentation construction for simplex restriction

This leaf deliberately does not import `Module.Component`. All local presentations
come from the one supplied total-site presentation. The generator image is evaluated on
the source chart and sent through the existing scheme pullback adjunction unit; its
extension to the target chart is the cokernel descent of the restricted presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open TopCat TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject.StagePresentation

variable (U : SimplicialObject Scheme.{u})

-- `Presentation` carries the sheafification assumptions of its actual slice site in
-- its type. Keep these providers local and tied to the exact total/stage slice
-- heads before elaborating later declaration types; native checking is still required.
local instance totalSliceWeakSheafify
    (X : DiagramOpens (forgetToTop.obj U)) :
    HasWeakSheafify
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
      AddCommGrpCat.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
    AddCommGrpCat.{u}).isRightAdjoint

local instance stageSliceWeakSheafify (n : SimplexCategoryᵒᵖ)
    (W : Opens ((forgetToTop.obj U).obj n)) :
    HasWeakSheafify ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
      AddCommGrpCat.{u} :=
  (CategoryTheory.plusPlusAdjunction
    ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
    AddCommGrpCat.{u}).isRightAdjoint

/-- The coefficient identification for stage restriction has identity components. -/
def ringIso (n : SimplexCategoryᵒᵖ) :
    (U.obj n).ringCatSheaf ≅
      ((DiagramOpens.fiber (forgetToTop.obj U) n).sheafPushforwardContinuous
        RingCat.{u} (Opens.grothendieckTopology ((forgetToTop.obj U).obj n))
          (CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U))).obj
            (structureSheaf U) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by sorry))

/-- Restriction to a stage, expressed using continuous module restriction. -/
def component (n : SimplexCategoryᵒᵖ) :
    SheafOfModules.{u} (structureSheaf U) ⥤ (U.obj n).Modules :=
  -- The coefficient sheaf fixes the scheme topology. Supply continuity directly:
  -- the forgotten TopCat carrier unfolds to this same scheme carrier.
  @SheafOfModules.pushforward.{u} _ _ _ _
    (Opens.grothendieckTopology (U.obj n))
    (CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U))
    (DiagramOpens.fiber (forgetToTop.obj U) n)
    (U.obj n).ringCatSheaf (structureSheaf U)
    (CategoryTheory.SimplicialObject.fiber_isContinuous (forgetToTop.obj U) n)
    (ringIso U n).hom

/-- Choose only the local presentation data already supplied by the actual QCoh input. -/
def inputData (F : QCoh U) : SheafOfModules.QuasicoherentData.{u, u} F.obj :=
  letI : F.obj.IsQuasicoherent := F.property
  SheafOfModules.IsQuasicoherent.nonempty_quasicoherentData.some

/-- A chart consists of an actual arrow into an object of the supplied presentation cover.
All such arrows are retained; no new presentation of a stage is chosen. -/
structure Chart {F : QCoh U} (q : SheafOfModules.QuasicoherentData.{u, u} F.obj)
    (n : SimplexCategoryᵒᵖ) where
  i : q.I
  W : Opens ((forgetToTop.obj U).obj n)
  a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ q.X i

/-- The actual total-slice functor associated with an arrow from a stage open. -/
def sliceFunctor {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    Over W ⥤ Over X :=
  Over.post (X := W) (DiagramOpens.fiber (forgetToTop.obj U) n) ⋙ Over.map a

instance sliceFunctor_isContinuous {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    (sliceFunctor U a).IsContinuous
      ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X) := by
  letI := CategoryTheory.SimplicialObject.fiber_isContinuous (forgetToTop.obj U) n
  -- Slice continuity is the same identity-stage covering calculation.
  sorry

instance sliceFunctor_isCocontinuous {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    (sliceFunctor U a).IsCocontinuous
      ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X) :=
  letI : (DiagramOpens.fiber (forgetToTop.obj U) n).IsCocontinuous
      (Opens.grothendieckTopology ((forgetToTop.obj U).obj n))
      (CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)) :=
    CategoryTheory.SimplicialObject.fiber_isCocontinuous (forgetToTop.obj U) n
  -- Infer `Over.post` at its native target, before transporting its proof term
  -- across the definitional equality `fiber.obj W = ofOpens ... n W`.
  let hpost : (Over.post (X := W) (DiagramOpens.fiber (forgetToTop.obj U) n)).IsCocontinuous
      ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over
        ((DiagramOpens.fiber (forgetToTop.obj U) n).obj W)) := inferInstance
  -- With abstract slice objects, the canonical `Over.map` provider matches
  -- directly. Instantiate its resulting term at `a`, without another search.
  let hmap : ∀ {Y Z : DiagramOpens (forgetToTop.obj U)} (f : Y ⟶ Z),
      (Over.map f).IsCocontinuous
        ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over Y)
        ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over Z) :=
    fun {_ _} f ↦ inferInstance
  @CategoryTheory.isCocontinuous_comp _ _ _ _ _ _
    (Over.post (X := W) (DiagramOpens.fiber (forgetToTop.obj U) n)) (Over.map a)
    ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
    ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over
      ((DiagramOpens.fiber (forgetToTop.obj U) n).obj W))
    ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
    hpost (hmap a)

/-- On a slice chart the coefficients are again identified by identity components.
The arrow `a` changes the slice object, never the coefficient at its domain. -/
def sliceRingIso {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    (U.obj n).ringCatSheaf.over W ≅
      ((sliceFunctor U a).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ((forgetToTop.obj U).obj n)).over W)
        ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)).obj
          ((structureSheaf U).over X) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by sorry))

/-- Restrict an actual module on the total slice to the stage slice. -/
def restriction {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    SheafOfModules.{u} ((structureSheaf U).over X) ⥤
      SheafOfModules.{u} ((U.obj n).ringCatSheaf.over W) :=
  @SheafOfModules.pushforward.{u} _ _ _ _
    ((Opens.grothendieckTopology (U.obj n)).over W)
    ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
    (sliceFunctor U a) ((U.obj n).ringCatSheaf.over W) ((structureSheaf U).over X)
    (sliceFunctor_isContinuous U a) (sliceRingIso U a).hom

/-- Restriction sends the coefficient module to the coefficient module, by identities. -/
def unitIso {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X) :
    SheafOfModules.unit ((U.obj n).ringCatSheaf.over W) ≅
      (restriction U a).obj (SheafOfModules.unit ((structureSheaf U).over X)) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun T ↦ ModuleCat.isoMk
        (R := ((U.obj n).ringCatSheaf.over W).obj.obj T)
        (M := (SheafOfModules.unit ((U.obj n).ringCatSheaf.over W)).val.obj T)
        (N := ((restriction U a).obj
          (SheafOfModules.unit ((structureSheaf U).over X))).val.obj T)
        (Iso.refl ((SheafOfModules.unit
          ((U.obj n).ringCatSheaf.over W)).val.presheaf.obj T))
        (by sorry)) (by sorry))

/-- Evaluation of a total-slice module agrees with evaluation of the stage module.
Both directions of this comparison are identity maps. -/
def restrictionIso {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X)
    (M : SheafOfModules.{u} (structureSheaf U)) :
    (restriction U a).obj (M.over X) ≅ ((component U n).obj M).over W :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk
      (fun T ↦ ModuleCat.isoMk
        (R := ((U.obj n).ringCatSheaf.over W).obj.obj T)
        (M := ((restriction U a).obj (M.over X)).val.obj T)
        (N := (((component U n).obj M).over W).val.obj T)
        (Iso.refl (((restriction U a).obj (M.over X)).val.presheaf.obj T))
        (by sorry)) (by sorry))

/-- The presentation on a stage slice is the image of the supplied total-slice
presentation. Colimit preservation uses the explicit descent in `ContinuousColimits`. -/
def presentation {n : SimplexCategoryᵒᵖ}
    {X : DiagramOpens (forgetToTop.obj U)}
    {W : Opens ((forgetToTop.obj U).obj n)}
    (a : DiagramOpens.ofOpens (forgetToTop.obj U) n W ⟶ X)
    {M : SheafOfModules.{u} (structureSheaf U)} (P : (M.over X).Presentation) :
    ((restriction U a).obj (M.over X)).Presentation :=
  -- Match the stage coefficient sheaf's exact scheme-slice topology head.
  -- The forgotten TopCat slice is definitionally equal, but its local instance
  -- need not match a search at this head under instance transparency.
  letI stageWeak : HasWeakSheafify
      ((Opens.grothendieckTopology (U.obj n)).over W)
      AddCommGrpCat.{u} :=
    (CategoryTheory.plusPlusAdjunction
      ((Opens.grothendieckTopology (U.obj n)).over W)
      AddCommGrpCat.{u}).isRightAdjoint
  letI totalWeak : HasWeakSheafify
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
      AddCommGrpCat.{u} :=
    (CategoryTheory.plusPlusAdjunction
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
      AddCommGrpCat.{u}).isRightAdjoint
  letI continuous : (sliceFunctor U a).IsContinuous
      ((Opens.grothendieckTopology (U.obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X) :=
    sliceFunctor_isContinuous U a
  letI cocontinuous : (sliceFunctor U a).IsCocontinuous
      ((Opens.grothendieckTopology (U.obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X) :=
    sliceFunctor_isCocontinuous U a
  let rightKan : ∀ Q : (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u},
      (sliceFunctor U a).op.HasPointwiseRightKanExtension Q :=
    fun Q ↦ inferInstance
  let stageLocallyBijective :
      ((Opens.grothendieckTopology (U.obj n)).over W).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let totalLocallyBijective :
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X).WEqualsLocallyBijective
        AddCommGrpCat.{u} := inferInstance
  let additiveColimits : HasColimitsOfSize.{u, u} AddCommGrpCat.{u} := inferInstance
  -- Pass the sheafification witnesses themselves: do not synthesize them while
  -- the module universe and the two slice topologies are still implicit.
  letI : PreservesColimitsOfSize.{u, u} (restriction U a) :=
    @SheafOfModules.ContinuousColimits.preservesColimitsOfSize
      (Over W) inferInstance (Over X) inferInstance
      ((Opens.grothendieckTopology (U.obj n)).over W)
      ((CategoryTheory.SimplicialObject.zariskiTopology (forgetToTop.obj U)).over X)
      (sliceFunctor U a) continuous cocontinuous rightKan
      stageWeak stageLocallyBijective totalWeak totalLocallyBijective
      ((structureSheaf U).over X) ((U.obj n).ringCatSheaf.over W)
      (sliceRingIso U a).hom additiveColimits
  P.map (restriction U a) (unitIso U a)

variable {n m : SimplexCategory} (φ : n ⟶ m) {F : QCoh U}
  (q : SheafOfModules.QuasicoherentData.{u, u} F.obj)

/-- The inverse-image open of a source chart. -/
def targetOpen (c : Chart U q (op n)) : Opens ((forgetToTop.obj U).obj (op m)) :=
  (Opens.map ((forgetToTop.obj U).map φ.op)).obj c.W

/-- The simplex arrow followed by the supplied chart arrow. -/
def targetArrow (c : Chart U q (op n)) :
    DiagramOpens.ofOpens (forgetToTop.obj U) (op m) (targetOpen U φ q c) ⟶ q.X c.i :=
  DiagramOpens.homMk φ.op (fun _ hx ↦ hx) ≫ c.a

/-- Both stage presentations use exactly `q.presentation c.i`, including its matrix. -/
def sourcePresentation (c : Chart U q (op n)) :=
  presentation U c.a (q.presentation c.i)

/-- The target presentation is the restriction of that same supplied presentation. -/
def targetPresentation (c : Chart U q (op n)) :=
  presentation U (targetArrow U φ q c) (q.presentation c.i)

/-- The sheaf in which local inverse images are to be glued. -/
def pullbackModule : (U.obj (op m)).Modules :=
  (Scheme.Modules.pullback (U.map φ.op)).obj ((component U (op n)).obj F.obj)

/-- A supplied generator, evaluated at the source chart and sent through the actual
pullback coevaluation. No local inverse is used in defining this element. -/
def generatorImage (c : Chart U q (op n))
    (j : (q.presentation c.i).generators.I) :
    (pullbackModule U φ (F := F)).val.obj (op (targetOpen U φ q c)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (U.map φ.op)).unit.app
    ((component U (op n)).obj F.obj)).val.app (op c.W)
      (show ((component U (op n)).obj F.obj).val.obj (op c.W) from by
        change F.obj.val.obj
          (op (DiagramOpens.ofOpens (forgetToTop.obj U) (op n) c.W))
        exact PresheafOfModules.sections.eval
          (M := (F.obj.over (q.X c.i)).val)
          ((q.presentation c.i).generators.s j) (op (Over.mk c.a)))

/-- The same generator can equivalently be evaluated in the transported source
presentation. This records that the two stage constructions use the same generators. -/
theorem generatorImage_sourcePresentation (c : Chart U q (op n))
    (j : (q.presentation c.i).generators.I) :
    generatorImage U φ q c j =
      ((Scheme.Modules.pullbackPushforwardAdjunction (U.map φ.op)).unit.app
        ((component U (op n)).obj F.obj)).val.app (op c.W)
          (show ((component U (op n)).obj F.obj).val.obj (op c.W) from
            (restrictionIso U c.a F.obj).hom.val.app (op (Over.mk (𝟙 c.W)))
              (PresheafOfModules.sections.eval
                (M := ((restriction U c.a).obj (F.obj.over (q.X c.i))).val)
                ((sourcePresentation U q c).generators.s j)
                (op (Over.mk (𝟙 c.W))))) := sorry

/-- Extend that section to all objects of the target slice by restriction. -/
def generatorSection (c : Chart U q (op n))
    (j : (q.presentation c.i).generators.I) :
    ((pullbackModule U φ (F := F)).over (targetOpen U φ q c)).sections :=
  PresheafOfModules.sectionsMk
    (fun T ↦ (pullbackModule U φ (F := F)).val.map T.unop.hom.op
      (generatorImage U φ q c j)) (by sorry)

/-- The generator map of the reverse, on the identical set of presentation generators. -/
def generatorMap (c : Chart U q (op n)) :
    SheafOfModules.free.{u}
      (R := (U.obj (op m)).ringCatSheaf.over (targetOpen U φ q c))
      (targetPresentation U φ q c).generators.I ⟶
      (pullbackModule U φ (F := F)).over (targetOpen U φ q c) :=
  (SheafOfModules.freeHomEquiv
    (M := (pullbackModule U φ (F := F)).over (targetOpen U φ q c))
    (I := (q.presentation c.i).generators.I)).symm
      (generatorSection U φ q c)

/-- The same supplied relation matrix annihilates the pulled-back source generators. -/
theorem relations_zero (c : Chart U q (op n)) :
    ((targetPresentation U φ q c).relations.π ≫
        kernel.ι (targetPresentation U φ q c).generators.π) ≫
      generatorMap U φ q c = 0 := sorry

/-- The local reverse is the ACTUAL cokernel descent of the target presentation. -/
def localReverse (c : Chart U q (op n)) :
    ((component U (op m)).obj F.obj).over (targetOpen U φ q c) ⟶
      (pullbackModule U φ (F := F)).over (targetOpen U φ q c) :=
  (restrictionIso U (targetArrow U φ q c) F.obj).inv ≫
    (targetPresentation U φ q c).isColimit.desc
      (CokernelCofork.ofπ (generatorMap U φ q c) (relations_zero U φ q c))

/-- The local reverse is characterized by its specified generator images. -/
theorem localReverse_generators (c : Chart U q (op n)) :
    (targetPresentation U φ q c).generators.π ≫
      (restrictionIso U (targetArrow U φ q c) F.obj).hom ≫ localReverse U φ q c =
        generatorMap U φ q c := sorry

/-- Covering sieve consisting of all subopens contained in an inverse-image chart. -/
def chartSieve (T : Opens ((forgetToTop.obj U).obj (op m))) : Sieve T where
  arrows := fun {V} _ ↦ ∃ c : Chart U q (op n), V ≤ targetOpen U φ q c
  downward_closed := by
    rintro V Z f ⟨c, hc⟩ g
    exact ⟨c, (leOfHom g).trans hc⟩

/-- The source charts cover by `q.coversTop`; their inverse images cover the target. -/
theorem chartSieve_mem (T : Opens ((forgetToTop.obj U).obj (op m))) :
    chartSieve U φ q T ∈ Opens.grothendieckTopology ((forgetToTop.obj U).obj (op m)) T := sorry

/-- Local images of a given section, on the actual covering sieve. The choice here only
unpacks membership `∃ c, V ≤ targetOpen c` in this explicitly defined sieve. -/
def localFamily {T : Opens ((forgetToTop.obj U).obj (op m))}
    (x : ((component U (op m)).obj F.obj).val.obj (op T)) :
    Presieve.FamilyOfElements
      ((pullbackModule U φ (F := F)).val.presheaf ⋙ forget AddCommGrpCat)
      (chartSieve U φ q T).arrows :=
  fun V f hf ↦
    let c := hf.choose
    let h := hf.choose_spec
    (localReverse U φ q c).val.app (op (Over.mk (homOfLE h)))
      (((component U (op m)).obj F.obj).val.map f.op x)

theorem localFamily_compatible {T : Opens ((forgetToTop.obj U).obj (op m))}
    (x : ((component U (op m)).obj F.obj).val.obj (op T)) :
    (localFamily U φ q x).Compatible := sorry

/-- The underlying type presheaf of the actual pullback module is a sheaf. -/
theorem pullback_isSheaf :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology ((forgetToTop.obj U).obj (op m)))
      ((pullbackModule U φ (F := F)).val.presheaf ⋙ forget AddCommGrpCat) :=
  CategoryTheory.Presheaf.isSheaf_comp_of_isSheaf _ _ _
    (pullbackModule U φ (F := F)).isSheaf

/-- Sectionwise gluing by the implemented sheaf amalgamation API. -/
def reverseSection (T : Opens ((forgetToTop.obj U).obj (op m)))
    (x : ((component U (op m)).obj F.obj).val.obj (op T)) :
    (pullbackModule U φ (F := F)).val.obj (op T) :=
  ((isSheaf_iff_isSheaf_of_type _ _).mp (pullback_isSheaf U φ (F := F)) _
    (chartSieve_mem U φ q T)).amalgamate (localFamily U φ q x)
      (localFamily_compatible U φ q x)

theorem reverseSection_restrict (T : Opens ((forgetToTop.obj U).obj (op m)))
    (x : ((component U (op m)).obj F.obj).val.obj (op T))
    {V : Opens ((forgetToTop.obj U).obj (op m))} (f : V ⟶ T)
    (hf : chartSieve U φ q T f) :
    (pullbackModule U φ (F := F)).val.map f.op (reverseSection U φ q T x) =
      localFamily U φ q x f hf :=
  Presieve.IsSheafFor.valid_glue _ (localFamily_compatible U φ q x) f hf

/-- Linear component of the glued reverse. -/
def reverseApp (q : SheafOfModules.QuasicoherentData.{u, u} F.obj)
    (T : (Opens ((forgetToTop.obj U).obj (op m)))ᵒᵖ) :
    ((component U (op m)).obj F.obj).val.obj T ⟶
      (pullbackModule U φ (F := F)).val.obj T :=
  @ModuleCat.ofHom
    ((U.obj (op m)).ringCatSheaf.obj.obj T) _
    (((component U (op m)).obj F.obj).val.obj T)
    ((pullbackModule U φ (F := F)).val.obj T)
    (((component U (op m)).obj F.obj).val.obj T).isAddCommGroup
    (((component U (op m)).obj F.obj).val.obj T).isModule
    ((pullbackModule U φ (F := F)).val.obj T).isAddCommGroup
    ((pullbackModule U φ (F := F)).val.obj T).isModule
    { toFun := reverseSection U φ q T.unop
      map_add' := by sorry
      map_smul' := by sorry }

/-- The reverse along an arbitrary simplex operator, constructed from the supplied
local presentation and sheaf amalgamation. -/
def reverse (q : SheafOfModules.QuasicoherentData.{u, u} F.obj) :
    (component U (op m)).obj F.obj ⟶ pullbackModule U φ (F := F) where
  val :=
    { app := reverseApp U φ q
      naturality := by sorry }

end AlgebraicGeometry.SimplicialObject.StagePresentation
