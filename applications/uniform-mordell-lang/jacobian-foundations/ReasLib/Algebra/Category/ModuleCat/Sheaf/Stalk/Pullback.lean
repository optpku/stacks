module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Skyscraper
public import ReasLib.Topology.Sheaves.Ring.Definition
public import ReasLib.Topology.Sheaves.Stalks.Pullback
import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalks of module pullbacks

This file owns the explicit stalk comparison for the inverse image of a sheaf of modules on a
topological space.  The comparison is built from the pullback--pushforward adjunction and the
stalk--skyscraper adjunction.  In particular, its inverse is data in this API rather than a map
selected from an `IsIso` proof.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
  TopCat TopologicalSpace Opposite

noncomputable section

universe u

namespace TopCat.Sheaf

variable {X Y : TopCat.{u}} (f : X ⟶ Y) (𝒪 : Y.Sheaf CommRingCat.{u})

/-- The commutative-ring sheaf on `X` obtained by pulling back `𝒪` along `f`. -/
@[stacks 008H "inverse-image commutative-ring sheaf"]
noncomputable abbrev pullbackRing : X.Sheaf CommRingCat.{u} :=
  (TopCat.Sheaf.pullback CommRingCat f).obj 𝒪

/-- The ring homomorphism on stalks induced by the canonical pullback stalk isomorphism. -/
@[stacks 008H "pullback stalk ring map"]
noncomputable abbrev pullbackStalkRingMap (x : X) :
    𝒪.presheaf.stalk (f x) →+* (pullbackRing f 𝒪).presheaf.stalk x :=
  (TopCat.Sheaf.stalkPullbackIso f 𝒪 x).hom.hom

variable (x : X)

section Skyscraper

variable (N : ModuleCat ((pullbackRing f 𝒪).presheaf.stalk x))

/-- The germ of the pullback unit followed by the pullback germ is the original germ followed by
the canonical map on stalks. -/
@[stacks 008H "pullback germ compatibility"]
theorem pullbackGerm_comp_unit (U : Opens Y) (h : f x ∈ U) :
    ((pullbackRing f 𝒪).presheaf.germ ((Opens.map f).obj U) x
        ((Opens.mem_map).2 h)).hom.comp
      ((commRingSheafPullbackUnit f 𝒪).hom.app (Opposite.op U)).hom =
    (pullbackStalkRingMap f 𝒪 x).comp (𝒪.presheaf.germ U (f x) h).hom := sorry

/-- Away from the image point, the zero maps on the two skyscraper sections compose to the
identity on the pushforward section. -/
@[stacks 007K "zero branch of the pushforward skyscraper comparison"]
theorem modulePullbackSkyscraperZero_hom_inv_id (U : Opens Y) (h : f x ∉ U) :
    (0 : ((PresheafOfModules.pushforward
      (commRingSheafPullbackUnit f 𝒪).hom).obj
        (PresheafOfModules.Skyscraper.atPoint (pullbackRing f 𝒪).presheaf x N)).obj
          (Opposite.op U) ⟶
      (PresheafOfModules.Skyscraper.atPoint 𝒪.presheaf (f x)
        ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N)).obj
          (Opposite.op U)) ≫ 0 = 𝟙 _ := sorry

/-- Away from the image point, the zero maps on the two skyscraper sections compose to the
identity on the target section. -/
@[stacks 007K "zero branch of the pushforward skyscraper comparison"]
theorem modulePullbackSkyscraperZero_inv_hom_id (U : Opens Y) (h : f x ∉ U) :
    (0 : (PresheafOfModules.Skyscraper.atPoint 𝒪.presheaf (f x)
      ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N)).obj
        (Opposite.op U) ⟶
      ((PresheafOfModules.pushforward
        (commRingSheafPullbackUnit f 𝒪).hom).obj
          (PresheafOfModules.Skyscraper.atPoint (pullbackRing f 𝒪).presheaf x N)).obj
            (Opposite.op U)) ≫ 0 = 𝟙 _ := sorry

/-- The sectionwise comparison between the pushforward of a module skyscraper on `X` and the
skyscraper on `Y` at `f x`. -/
@[stacks 007K "pushforward of a module skyscraper"]
noncomputable def modulePullbackSkyscraperAppIso (U : Opens Y) :
    ((PresheafOfModules.pushforward
      (commRingSheafPullbackUnit f 𝒪).hom).obj
        (PresheafOfModules.Skyscraper.atPoint (pullbackRing f 𝒪).presheaf x N)).obj
      (Opposite.op U) ≅
    (PresheafOfModules.Skyscraper.atPoint 𝒪.presheaf (f x)
      ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N)).obj
      (Opposite.op U) :=
  @dite (_ ≅ _) (f x ∈ U) (Classical.dec _)
    (fun h =>
      eqToIso (congrArg
        (fun M : ModuleCat
            ((pullbackRing f 𝒪).presheaf.obj
              (Opposite.op ((Opens.map f).obj U))) =>
          (ModuleCat.restrictScalars
            ((commRingSheafPullbackUnit f 𝒪).hom.app (Opposite.op U)).hom).obj M)
        (PresheafOfModules.Skyscraper.obj_eq_of_mem
          (pullbackRing f 𝒪).presheaf x N
          (Opposite.op ((Opens.map f).obj U)) ((Opens.mem_map).2 h))) ≪≫
      (ModuleCat.restrictScalarsComp'App
        ((commRingSheafPullbackUnit f 𝒪).hom.app (Opposite.op U)).hom
        ((pullbackRing f 𝒪).presheaf.germ
          ((Opens.map f).obj U) x ((Opens.mem_map).2 h)).hom
        (((pullbackRing f 𝒪).presheaf.germ
          ((Opens.map f).obj U) x ((Opens.mem_map).2 h)).hom.comp
          ((commRingSheafPullbackUnit f 𝒪).hom.app (Opposite.op U)).hom) rfl N).symm ≪≫
      (ModuleCat.restrictScalarsCongr (pullbackGerm_comp_unit f 𝒪 x U h)).app N ≪≫
      (ModuleCat.restrictScalarsComp'App
        (𝒪.presheaf.germ U (f x) h).hom
        (pullbackStalkRingMap f 𝒪 x)
        ((pullbackStalkRingMap f 𝒪 x).comp
          (𝒪.presheaf.germ U (f x) h).hom) rfl N) ≪≫
      eqToIso (PresheafOfModules.Skyscraper.obj_eq_of_mem 𝒪.presheaf (f x)
        ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N)
        (Opposite.op U) h).symm)
    (fun h =>
      { hom := 0
        inv := 0
        hom_inv_id := modulePullbackSkyscraperZero_hom_inv_id f 𝒪 x N U h
        inv_hom_id := modulePullbackSkyscraperZero_inv_hom_id f 𝒪 x N U h })

/-- The sectionwise skyscraper comparison is compatible with restriction maps. -/
@[stacks 007K "pushforward module skyscraper naturality"]
theorem modulePullbackSkyscraperAppIso_naturality
    {U V : (Opens Y)ᵒᵖ} (i : U ⟶ V) :
    ((PresheafOfModules.pushforward
      (commRingSheafPullbackUnit f 𝒪).hom).obj
        (PresheafOfModules.Skyscraper.atPoint (pullbackRing f 𝒪).presheaf x N)).map i ≫
        (ModuleCat.restrictScalars
          (((𝒪.ringSheafOfComm).obj.map i).hom)).map
          (modulePullbackSkyscraperAppIso f 𝒪 x N V.unop).hom =
      (modulePullbackSkyscraperAppIso f 𝒪 x N U.unop).hom ≫
        (PresheafOfModules.Skyscraper.atPoint 𝒪.presheaf (f x)
          ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N)).map i := sorry

/-- The pushforward of a module skyscraper is canonically the skyscraper at the image point. -/
@[stacks 007K "pushforward module skyscraper isomorphism"]
noncomputable def modulePullbackSkyscraperIso :
    (SheafOfModules.pushforward (commRingSheafPullbackUnit f 𝒪)).obj
        (PresheafOfModules.Skyscraper.sheafAtPoint (pullbackRing f 𝒪) x N) ≅
      PresheafOfModules.Skyscraper.sheafAtPoint 𝒪 (f x)
        ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj N) :=
  (SheafOfModules.fullyFaithfulForget 𝒪.ringSheafOfComm).preimageIso
    (PresheafOfModules.isoMk
      (fun U ↦ modulePullbackSkyscraperAppIso f 𝒪 x N U.unop)
      (fun _ _ i ↦ modulePullbackSkyscraperAppIso_naturality f 𝒪 x N i))

end Skyscraper

section Comparison

variable (M : SheafOfModules 𝒪.ringSheafOfComm)

/-- Take a module-sheaf stalk at `f x` and extend scalars along the pullback map on local
rings. -/
@[stacks 05V5 "module pullback stalk source functor"]
noncomputable abbrev modulePullbackStalkSource :
    SheafOfModules 𝒪.ringSheafOfComm ⥤
      ModuleCat ((pullbackRing f 𝒪).presheaf.stalk x) :=
  SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x) ⋙
    ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)

/-- Pull back a module sheaf and then take its stalk at `x`. -/
@[stacks 05V5 "module pullback stalk target functor"]
noncomputable abbrev modulePullbackStalkTarget :
    SheafOfModules 𝒪.ringSheafOfComm ⥤
      ModuleCat ((pullbackRing f 𝒪).presheaf.stalk x) :=
  SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪) ⋙
    SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x

/-- The additive map on stalks induced by the unit of the module pullback--pushforward
adjunction. -/
@[stacks 05V5 "module pullback stalk unit"]
noncomputable def modulePullbackUnitAdd :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (f x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M).val.presheaf x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).map
      ((SheafOfModules.toSheaf 𝒪.ringSheafOfComm).map
        ((SheafOfModules.pullbackPushforwardAdjunction
          (commRingSheafPullbackUnit f 𝒪)).unit.app M)).hom ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f
      ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M).val.presheaf x

/-- The unit-induced stalk map is semilinear for `pullbackStalkRingMap`. -/
@[stacks 05V5 "module pullback stalk unit semilinearity"]
theorem modulePullbackUnitAdd_smul
    (r : 𝒪.presheaf.stalk (f x))
    (m : TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) M.val.presheaf (f x)) :
    modulePullbackUnitAdd f 𝒪 x M (r • m) =
      pullbackStalkRingMap f 𝒪 x r • modulePullbackUnitAdd f 𝒪 x M m := sorry

/-- The unit-induced stalk map viewed as a morphism into restriction of scalars. -/
@[stacks 05V5 "restricted module pullback stalk unit"]
noncomputable def modulePullbackUnit :
    (SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M ⟶
      (ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj
        ((SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x).obj
          ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M)) :=
  (ModuleCat.semilinearMapAddEquiv (pullbackStalkRingMap f 𝒪 x)
    ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M)
    ((SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x).obj
      ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M)))
    { toFun := modulePullbackUnitAdd f 𝒪 x M
      map_add' := (modulePullbackUnitAdd f 𝒪 x M).hom.map_add
      map_smul' := modulePullbackUnitAdd_smul f 𝒪 x M }

/-- The canonical scalar-extension comparison from a module stalk to its pullback stalk. -/
@[stacks 05V5 "module pullback stalk comparison"]
noncomputable def modulePullbackStalkComparison :
    (ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
        ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M) ⟶
      (SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x).obj
        ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M) :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (pullbackStalkRingMap f 𝒪 x) (modulePullbackUnit f 𝒪 x M)

/-- The explicit inverse of the module pullback stalk comparison. -/
@[stacks 05V5 "inverse module pullback stalk comparison"]
noncomputable def modulePullbackStalkComparisonInv :
    (SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x).obj
        ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M) ⟶
      (ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
        ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M) :=
  (PresheafOfModules.Skyscraper.sheafHomEquiv (pullbackRing f 𝒪) x
    ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M)
    ((ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
      ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M))).symm
    (((SheafOfModules.pullbackPushforwardAdjunction
      (commRingSheafPullbackUnit f 𝒪)).homEquiv M
      (PresheafOfModules.Skyscraper.sheafAtPoint (pullbackRing f 𝒪) x
        ((ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
          ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M)))).symm
      ((PresheafOfModules.Skyscraper.sheafHomEquiv 𝒪 (f x) M
          ((ModuleCat.restrictScalars (pullbackStalkRingMap f 𝒪 x)).obj
            ((ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
              ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M))))
        ((ModuleCat.extendRestrictScalarsAdj (pullbackStalkRingMap f 𝒪 x)).unit.app
          ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M)) ≫
        (modulePullbackSkyscraperIso f 𝒪 x
          ((ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
            ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M))).inv))

/-- The pullback stalk comparison followed by its explicit inverse is the identity. -/
@[simp, stacks 05V5 "module pullback stalk forward-inverse law"]
theorem modulePullbackStalkComparison_hom_inv_id :
    modulePullbackStalkComparison f 𝒪 x M ≫
      modulePullbackStalkComparisonInv f 𝒪 x M = 𝟙 _ := sorry

/-- The explicit inverse followed by the pullback stalk comparison is the identity. -/
@[simp, stacks 05V5 "module pullback stalk inverse-forward law"]
theorem modulePullbackStalkComparison_inv_hom_id :
    modulePullbackStalkComparisonInv f 𝒪 x M ≫
      modulePullbackStalkComparison f 𝒪 x M = 𝟙 _ := sorry

/-- The explicit stalk isomorphism for inverse image of a module sheaf. -/
@[stacks 05V5 "module pullback stalk isomorphism"]
noncomputable def modulePullbackStalkIso :
    (ModuleCat.extendScalars (pullbackStalkRingMap f 𝒪 x)).obj
        ((SheafOfModules.stalkFunctorOfCommRing 𝒪 (f x)).obj M) ≅
      (SheafOfModules.stalkFunctorOfCommRing (pullbackRing f 𝒪) x).obj
        ((SheafOfModules.pullback (commRingSheafPullbackUnit f 𝒪)).obj M) where
  hom := modulePullbackStalkComparison f 𝒪 x M
  inv := modulePullbackStalkComparisonInv f 𝒪 x M
  hom_inv_id := modulePullbackStalkComparison_hom_inv_id f 𝒪 x M
  inv_hom_id := modulePullbackStalkComparison_inv_hom_id f 𝒪 x M

/-- The module pullback stalk comparison is canonically invertible. -/
@[stacks 05V5 "module pullback stalk comparison isomorphism", instance]
instance modulePullbackStalkComparison_isIso :
    IsIso (modulePullbackStalkComparison f 𝒪 x M) := sorry

/-- The forward map of the module pullback stalk isomorphism is the canonical comparison. -/
@[simp, stacks 05V5 "module pullback stalk isomorphism hom"]
theorem modulePullbackStalkIso_hom :
    (modulePullbackStalkIso f 𝒪 x M).hom =
      modulePullbackStalkComparison f 𝒪 x M := sorry

/-- The inverse map of the module pullback stalk isomorphism is the explicit comparison
inverse. -/
@[simp, stacks 05V5 "module pullback stalk isomorphism inverse"]
theorem modulePullbackStalkIso_inv :
    (modulePullbackStalkIso f 𝒪 x M).inv =
      modulePullbackStalkComparisonInv f 𝒪 x M := sorry

/-- The module pullback stalk comparison is natural in the module sheaf. -/
@[reassoc, stacks 05V5 "module pullback stalk comparison naturality"]
theorem modulePullbackStalkComparison_naturality
    {M N : SheafOfModules 𝒪.ringSheafOfComm} (φ : M ⟶ N) :
    (modulePullbackStalkSource f 𝒪 x).map φ ≫
        modulePullbackStalkComparison f 𝒪 x N =
      modulePullbackStalkComparison f 𝒪 x M ≫
        (modulePullbackStalkTarget f 𝒪 x).map φ := sorry

/-- The explicit inverse module pullback stalk comparison is natural in the module sheaf. -/
@[reassoc, stacks 05V5 "module pullback stalk inverse naturality"]
theorem modulePullbackStalkComparisonInv_naturality
    {M N : SheafOfModules 𝒪.ringSheafOfComm} (φ : M ⟶ N) :
    (modulePullbackStalkTarget f 𝒪 x).map φ ≫
        modulePullbackStalkComparisonInv f 𝒪 x N =
      modulePullbackStalkComparisonInv f 𝒪 x M ≫
        (modulePullbackStalkSource f 𝒪 x).map φ := sorry

/-- The forward natural transformation for the module pullback stalk comparison. -/
@[stacks 05V5 "natural module pullback stalk comparison"]
noncomputable def modulePullbackStalkNatTrans :
    modulePullbackStalkSource f 𝒪 x ⟶ modulePullbackStalkTarget f 𝒪 x where
  app M := modulePullbackStalkComparison f 𝒪 x M
  naturality _ _ φ := modulePullbackStalkComparison_naturality f 𝒪 x φ

/-- The inverse natural transformation for the module pullback stalk comparison. -/
@[stacks 05V5 "natural inverse module pullback stalk comparison"]
noncomputable def modulePullbackStalkInvNatTrans :
    modulePullbackStalkTarget f 𝒪 x ⟶ modulePullbackStalkSource f 𝒪 x where
  app M := modulePullbackStalkComparisonInv f 𝒪 x M
  naturality _ _ φ := modulePullbackStalkComparisonInv_naturality f 𝒪 x φ

/-- The forward and inverse module pullback stalk transformations compose to the identity. -/
@[simp, stacks 05V5 "module pullback stalk natural forward-inverse law"]
theorem modulePullbackStalkNatTrans_hom_inv_id :
    modulePullbackStalkNatTrans f 𝒪 x ≫ modulePullbackStalkInvNatTrans f 𝒪 x = 𝟙 _ := sorry

/-- The inverse and forward module pullback stalk transformations compose to the identity. -/
@[simp, stacks 05V5 "module pullback stalk natural inverse-forward law"]
theorem modulePullbackStalkNatTrans_inv_hom_id :
    modulePullbackStalkInvNatTrans f 𝒪 x ≫ modulePullbackStalkNatTrans f 𝒪 x = 𝟙 _ := sorry

/-- Pullback of module sheaves commutes naturally with taking stalks and extending local
scalars. -/
@[stacks 05V5 "module pullback stalk natural isomorphism"]
noncomputable def modulePullbackStalkNatIso :
    modulePullbackStalkSource f 𝒪 x ≅ modulePullbackStalkTarget f 𝒪 x :=
  { hom := modulePullbackStalkNatTrans f 𝒪 x
    inv := modulePullbackStalkInvNatTrans f 𝒪 x
    hom_inv_id := modulePullbackStalkNatTrans_hom_inv_id f 𝒪 x
    inv_hom_id := modulePullbackStalkNatTrans_inv_hom_id f 𝒪 x }

/-- The component of `modulePullbackStalkNatIso` is the objectwise explicit stalk
isomorphism. -/
@[simp, stacks 05V5 "module pullback stalk natural isomorphism component"]
theorem modulePullbackStalkNatIso_app :
    (modulePullbackStalkNatIso f 𝒪 x).app M =
      modulePullbackStalkIso f 𝒪 x M := sorry

/-- The forward natural transformation of the module pullback stalk natural isomorphism. -/
@[simp, stacks 05V5 "module pullback stalk natural isomorphism hom"]
theorem modulePullbackStalkNatIso_hom :
    (modulePullbackStalkNatIso f 𝒪 x).hom = modulePullbackStalkNatTrans f 𝒪 x := sorry

/-- The inverse natural transformation of the module pullback stalk natural isomorphism. -/
@[simp, stacks 05V5 "module pullback stalk natural isomorphism inverse"]
theorem modulePullbackStalkNatIso_inv :
    (modulePullbackStalkNatIso f 𝒪 x).inv = modulePullbackStalkInvNatTrans f 𝒪 x := sorry

/-- The forward component of the module pullback stalk natural isomorphism is the named
comparison. -/
@[simp, stacks 05V5 "module pullback stalk natural isomorphism hom component"]
theorem modulePullbackStalkNatIso_hom_app :
    (modulePullbackStalkNatIso f 𝒪 x).hom.app M =
      modulePullbackStalkComparison f 𝒪 x M := sorry

/-- The inverse component of the module pullback stalk natural isomorphism is the named explicit
inverse comparison. -/
@[simp, stacks 05V5 "module pullback stalk natural isomorphism inverse component"]
theorem modulePullbackStalkNatIso_inv_app :
    (modulePullbackStalkNatIso f 𝒪 x).inv.app M =
      modulePullbackStalkComparisonInv f 𝒪 x M := sorry

end Comparison

end TopCat.Sheaf
