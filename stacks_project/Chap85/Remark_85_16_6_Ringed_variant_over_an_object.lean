module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial.Module
public import ReasLib.CategoryTheory.Sites.Family.FormalCoproduct
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits Opposite
open RingedSite.Localization
open SemiRepresentableFamily (OverSite overTopology overSiteDiagram overSiteTotalTopology
  totalForget overMap)
open scoped SemiRepresentableFamily Simplicial

universe ι u v w z

section

variable {S : RingedSite.{u, v, w}} (X : S)
variable (K : SimplicialObject (FormalCoproduct.{ι} (CategoryTheory.Over X)))

/- The slice ringed site carries the restricted structure sheaf O_X. -/

#check (RingedSite.localization S X :
  RingedSite.{max u v, v, w})

#check ((RingedSite.localization S X).structureSheaf :
  Sheaf (S.siteTopology.over X) RingCat.{w})

#check (CategoryTheory.SemiRepresentableFamily.OverFamily.{v, u, ι} X :
  Type (max (ι + 1) u v))

/- K determines the slice category; the named ambient ringed site also fixes
its topology and coefficients in each canonical construction. -/

/- Remark 85.16.6 (Ringed variant over an object): the total ringed site for a
simplicial semi-representable family over X. -/

@[stacks 0D9X] #check (RingedSite.Localization.AtSimplicialSR.site (X := RingedSite.localization S X) K :
  RingedSite.{max ι u v, max ι u v, w})

#check (AtSimplicialSR.structureSheaf_spec (X := RingedSite.localization S X) K :
  (AtSimplicialSR.site (X := RingedSite.localization S X) K).structureSheaf =
    RingedSite.Cocontinuous.inverseImageRingSheaf
      (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X))

section TotalMorphisms

variable [UnivLE.{max ι u v, w}]

variable [HasSheafify (overSiteTotalTopology (S.siteTopology.over X) K) (Type w)]

variable [∀ P : (Grothendieck (overSiteDiagram K))ᵒᵖ ⥤ Type w,
  (totalForget K).op.HasPointwiseRightKanExtension P]

variable [(overSiteTotalTopology (S.siteTopology.over X) K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

variable [(S.siteTopology.over X).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- The total augmentation lands in the ringed slice over X and is flat. -/

#check (AtSimplicialSR.toAmbient (X := RingedSite.localization S X) K :
  RingedSite.ToposHom (AtSimplicialSR.site (X := RingedSite.localization S X) K)
    (RingedSite.localization S X))

#check (AtSimplicialSR.toAmbient_isFlat (X := RingedSite.localization S X) K :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.toAmbient (X := RingedSite.localization S X) K))

end TotalMorphisms

section TotalModules

/- The source topology is explicit because totalForget alone does not determine
it. Total lower shriek is left adjoint to inverse image. -/

#check (RingedSite.Cocontinuous.moduleLowerShriek
    (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X) :
  SheafOfModules.{z} (AtSimplicialSR.ringSheaf (X := RingedSite.localization S X) K) ⥤
    SheafOfModules.{z} (S.structureSheaf.over X))

#check (RingedSite.Cocontinuous.moduleInverseImage
    (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X) :
  SheafOfModules.{z} (S.structureSheaf.over X) ⥤
    SheafOfModules.{z} (AtSimplicialSR.ringSheaf (X := RingedSite.localization S X) K))

#check (RingedSite.Cocontinuous.moduleLowerShriek.adjunction
  (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X) :
  (RingedSite.Cocontinuous.moduleLowerShriek
    (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X) :
    SheafOfModules.{z} (AtSimplicialSR.ringSheaf (X := RingedSite.localization S X) K) ⥤
      SheafOfModules.{z} (S.structureSheaf.over X)) ⊣
    RingedSite.Cocontinuous.moduleInverseImage
    (J := (overSiteTotalTopology (S.siteTopology.over X) K)) (totalForget K) (S.structureSheaf.over X))

end TotalModules

section DegreeMorphisms

variable (n : SimplexCategory)

section RingedMorphisms

variable [UnivLE.{max ι u v, w}]

variable [HasSheafify (overTopology (S.siteTopology.over X) (K.obj (op n))) (Type w)]

variable [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
  (SemiRepresentableFamily.forget (K.obj (op n))).op.HasPointwiseRightKanExtension P]

variable [(overTopology (S.siteTopology.over X) (K.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

variable [(S.siteTopology.over X).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- Each degree augmentation lands in the same ringed slice and is flat. -/

variable [h_forget : (SemiRepresentableFamily.forget (K.obj (op n))).IsCocontinuous
  (AtSR.site (X := RingedSite.localization S X) (K.obj (op n))).siteTopology
  (RingedSite.localization S X).siteTopology]

#check (AtSimplicialSR.stageToAmbient (X := RingedSite.localization S X) K n :
  RingedSite.ToposHom (AtSR.site (X := RingedSite.localization S X) (K.obj (op n)))
    (RingedSite.localization S X))

#check (AtSimplicialSR.stageToAmbient_isFlat (X := RingedSite.localization S X) K n :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageToAmbient (X := RingedSite.localization S X) K n))

end RingedMorphisms

section Modules

variable [UnivLE.{max ι v, z}]

variable [HasWeakSheafify (S.siteTopology.over X) AddCommGrpCat.{z}]

variable [(S.siteTopology.over X).WEqualsLocallyBijective AddCommGrpCat.{z}]

/- Degree lower shriek is exact and left adjoint to restriction. -/

#check (AtSR.moduleLowerShriekAdjunction (X := RingedSite.localization S X) (K.obj (op n)) :
  (AtSR.moduleLowerShriek (X := RingedSite.localization S X) (K.obj (op n)) :
    SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))) ⥤
      SheafOfModules.{z} (S.structureSheaf.over X)) ⊣
    RingedSite.Cocontinuous.moduleInverseImage
      (J := (overTopology (S.siteTopology.over X) (K.obj (op n))))
      (SemiRepresentableFamily.forget (K.obj (op n))) (S.structureSheaf.over X))

#check (AtSR.moduleLowerShriek_exact (X := RingedSite.localization S X) (K.obj (op n)) :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))))
    (SheafOfModules.{z} (S.structureSheaf.over X))
    (AtSR.moduleLowerShriek (X := RingedSite.localization S X) (K.obj (op n))))

end Modules

end DegreeMorphisms

section Operators

variable {m n : SimplexCategory} (φ : m ⟶ n)

section RingedMorphisms

variable [UnivLE.{max ι u v, w}]

variable [HasSheafify (overTopology (S.siteTopology.over X) (K.obj (op n))) (Type w)]

variable [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
  (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]

variable [(overTopology (S.siteTopology.over X) (K.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

variable [(overTopology (S.siteTopology.over X) (K.obj (op m))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- A simplex operator m ⟶ n induces a flat morphism from degree n to degree m. -/

variable [h_map : (overMap (K.map φ.op)).IsCocontinuous
  (AtSR.site (X := RingedSite.localization S X) (K.obj (op n))).siteTopology
  (AtSR.site (X := RingedSite.localization S X) (K.obj (op m))).siteTopology]

#check (AtSimplicialSR.stageMap (X := RingedSite.localization S X) K φ :
  RingedSite.ToposHom (AtSR.site (X := RingedSite.localization S X) (K.obj (op n)))
    (AtSR.site (X := RingedSite.localization S X) (K.obj (op m))))

#check (AtSimplicialSR.stageMap_isFlat (X := RingedSite.localization S X) K φ :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageMap (X := RingedSite.localization S X) K φ))

end RingedMorphisms

section Modules

variable [UnivLE.{max ι v, z}]

variable [HasWeakSheafify (overTopology (S.siteTopology.over X) (K.obj (op m))) AddCommGrpCat.{z}]

variable [(overTopology (S.siteTopology.over X) (K.obj (op m))).WEqualsLocallyBijective AddCommGrpCat.{z}]

/- Operator lower shriek has the same covariant direction, is exact, and is
left adjoint to module pullback. -/

#check (AtSR.mapModuleLowerShriek_adjunction (X := RingedSite.localization S X) (K.map φ.op) :
  (AtSR.mapModuleLowerShriek (X := RingedSite.localization S X) (K.map φ.op) :
    SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))) ⥤
      SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op m)))) ⊣
    AtSR.mapModulePullback (X := RingedSite.localization S X) (K.map φ.op))

#check (AtSR.map_moduleLowerShriek_exact (X := RingedSite.localization S X) (K.map φ.op) :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))))
    (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op m))))
    (AtSR.mapModuleLowerShriek (X := RingedSite.localization S X) (K.map φ.op)))

end Modules

end Operators

section Fibers

variable (n : SimplexCategory)

section RingedMorphisms

variable [UnivLE.{max ι u v, w}]

variable [HasSheafify (overTopology (S.siteTopology.over X) (K.obj (op n))) (Type w)]

variable [∀ P : (OverSite (K.obj (op n)))ᵒᵖ ⥤ Type w,
  (Grothendieck.ι (overSiteDiagram K) (op n)).op.HasPointwiseRightKanExtension P]

variable [(overTopology (S.siteTopology.over X) (K.obj (op n))).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

variable [(overSiteTotalTopology (S.siteTopology.over X) K).HasSheafCompose (CategoryTheory.forget RingCat.{w})]

/- Each fiber inclusion into the total ringed site is flat. -/

#check (AtSimplicialSR.stageIncl (X := RingedSite.localization S X) K n :
  RingedSite.ToposHom (AtSR.site (X := RingedSite.localization S X) (K.obj (op n)))
    (AtSimplicialSR.site (X := RingedSite.localization S X) K))

#check (AtSimplicialSR.stageIncl_isFlat (X := RingedSite.localization S X) K n :
  RingedSite.ToposHom.IsFlat (AtSimplicialSR.stageIncl (X := RingedSite.localization S X) K n))

end RingedMorphisms

/- The fiber adjunction uses the canonical identification of restricted coefficients. -/

#check (AtSimplicialSR.stageInclModuleLowerShriek_adjunction (X := RingedSite.localization S X) K n :
  (AtSimplicialSR.stageInclModuleLowerShriek (X := RingedSite.localization S X) K n :
    SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))) ⥤
      SheafOfModules.{z} (AtSimplicialSR.ringSheaf (X := RingedSite.localization S X) K)) ⊣
    AtSimplicialSR.stageInclModuleInverseImage (X := RingedSite.localization S X) K n)

section Exactness

variable [UnivLE.{max ι u v, w}]

variable [UnivLE.{max ι v, z}]

variable [HasWeakSheafify (overSiteTotalTopology (S.siteTopology.over X) K) AddCommGrpCat.{z}]

variable [(overSiteTotalTopology (S.siteTopology.over X) K).WEqualsLocallyBijective AddCommGrpCat.{z}]

variable [∀ m, HasSheafify (overTopology (S.siteTopology.over X) (K.obj (op m))) (Type w)]

variable [∀ {m : SimplexCategory} (φ : n ⟶ m) (P : (OverSite (K.obj (op m)))ᵒᵖ ⥤ Type w),
  (overMap (K.map φ.op)).op.HasPointwiseRightKanExtension P]

variable [∀ m, (overTopology (S.siteTopology.over X) (K.obj (op m))).HasSheafCompose
  (CategoryTheory.forget RingCat.{w})]

variable [∀ {m : SimplexCategory} (φ : n ⟶ m),
  (overMap (K.map φ.op)).IsCocontinuous
    (overTopology (S.siteTopology.over X) (K.obj (op m)))
    (overTopology (S.siteTopology.over X) (K.obj (op n)))]

/- Fiber lower shriek, with its canonical coefficient transport, is exact. -/

#check (AtSimplicialSR.stageIncl_moduleLowerShriek_exact (X := RingedSite.localization S X) K n :
  CategoryTheory.exactFunctor
    (SheafOfModules.{z} (AtSR.ringSheaf (X := RingedSite.localization S X) (K.obj (op n))))
    (SheafOfModules.{z} (AtSimplicialSR.ringSheaf (X := RingedSite.localization S X) K))
    (AtSimplicialSR.stageInclModuleLowerShriek (X := RingedSite.localization S X) K n))

end Exactness

end Fibers

end
