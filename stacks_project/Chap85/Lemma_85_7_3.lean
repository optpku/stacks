module

public import ReasLib.AlgebraicGeometry.RingedSite.Simplicial.DerivedMorphism
import StacksCheckRecall

/-!
# Lemma 85.7.3

With notation and hypotheses as in Lemma 85.7.2, for `K` in `D(O)` one has
`(g'_n)^* (R h_total,* K) = R h_n,* (g_n^* K)` in `D(O'_n)`. The same identity
holds in Situation 85.3.3 case A and case B.
-/

@[expose] public section

universe u v w

open CategoryTheory Opposite RingedSite RingedSite.ToposHom
open scoped MorphismOfTopoiIn

section

open CategoryTheory.SimplicialSites

variable {C C' : SimplexCategory ⥤ Cat.{v, u}}
variable (J : ∀ n, Precoverage (C.obj n)) (J' : ∀ n, Precoverage (C'.obj n))
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C.obj m)ᵒᵖ ⥤ Type w),
    ((C.map φ).toFunctor).op.HasLeftKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (C'.obj m)ᵒᵖ ⥤ Type w),
    ((C'.map φ).toFunctor).op.HasLeftKanExtension P]
variable [IsMorphismDiagram C J] [IsMorphismDiagram C' J']
variable [HasWeakSheafify (topology C J) (Type w)]
variable [HasWeakSheafify (topology C' J') (Type w)]
variable (O : Sheaf (topology C J) RingCat.{w})
variable (O' : Sheaf (topology C' J') RingCat.{w})
variable [(topology C J).HasSheafCompose (forget RingCat.{w})]
variable [(topology C' J').HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (forget RingCat.{w})]
variable [∀ n, HasSheafify ((J n).toGrothendieck) (Type w)]
variable [∀ n, HasSheafify ((J' n).toGrothendieck) (Type w)]
variable [HasSheafify (topology C J) (Type w)]
variable [HasSheafify (topology C' J') (Type w)]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (C.obj n)ᵒᵖ ⥤ Type w, (ofStage C n).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (C'.obj n)ᵒᵖ ⥤ Type w, (ofStage C' n).op.HasPointwiseRightKanExtension P]

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (C'.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasLeftKanExtension P]
variable [∀ P : (totalSite C')ᵒᵖ ⥤ Type w,
    (IsMorphism.totalFunctor f.toSimplicial).op.HasLeftKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (stageMorphism C' J' O' n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [HasModulePushforwardDerived (SimplicialSites.RingedMorphism.toToposHom f)]
variable [∀ n, HasModulePushforwardDerived (SimplicialSites.RingedMorphism.topos f n)]

/- Lemma 85.7.3 (1)
In Situation 85.3.3 case A, restriction to each stage commutes
with unbounded derived direct image of modules. -/
@[stacks 0DH1] #check
  (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_hom_isIso f :
    ∀ (n : SimplexCategory),
      IsIso (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_hom f n))

#check (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_hom f :
  ∀ (n : SimplexCategory),
    modulePushforwardDerived (SimplicialSites.RingedMorphism.toToposHom f) ⋙
        SimplicialSites.derivedModuleRestrict C' J' O' n ⟶
      SimplicialSites.derivedModuleRestrict C J O n ⋙
        modulePushforwardDerived (SimplicialSites.RingedMorphism.topos f n))

#check (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_obj_isIso f :
  ∀ (n : SimplexCategory) (K : Hom.ModuleDerived.{w} (totalRingedSite C J O)),
    IsIso (CategoryTheory.SimplicialSites.RingedMorphism.restrict_modulePushforwardDerived_obj f n K))

end

section

open CategoryTheory.Grothendieck

variable {F F' : SimplicialObject Cat.{v, u}}
variable (J : ∀ n, Precoverage (F.obj n)) (J' : ∀ n, Precoverage (F'.obj n))
variable [IsFiberwiseSite F J] [IsFiberwiseSite F' J']
variable [∀ n, HasSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasSheafify (J' n).toGrothendieck (Type w)]
variable [HasSheafify (topology F J) (Type w)]
variable [HasSheafify (topology F' J') (Type w)]
variable [HasWeakSheafify (topology F J) (Type w)]
variable [HasWeakSheafify (topology F' J') (Type w)]
variable [∀ n, HasWeakSheafify (J n).toGrothendieck (Type w)]
variable [∀ n, HasWeakSheafify (J' n).toGrothendieck (Type w)]
variable (O : Sheaf (topology F J) RingCat.{w})
variable (O' : Sheaf (topology F' J') RingCat.{w})
variable [(topology F J).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [(topology F' J').HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ((J' n).toGrothendieck).HasSheafCompose (CategoryTheory.forget RingCat.{w})]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasLeftKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F'.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F.obj (op n))ᵒᵖ ⥤ Type w),
    ((F.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ (m n : SimplexCategory) (φ : m ⟶ n) (P : (F'.obj (op n))ᵒᵖ ⥤ Type w),
    ((F'.map φ.op).toFunctor).op.HasPointwiseRightKanExtension P]

variable {J J' O O'}
variable (f : RingedMorphism J J' O O')
variable [∀ n (P : (F.obj n)ᵒᵖ ⥤ Type w),
    ((f.toSimplicial.app n).toFunctor).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Grothendieck F)ᵒᵖ ⥤ Type w,
    (Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    ((f.toSimplicial.app (op n)).toFunctor ⋙ ι F' (op n)).op.HasPointwiseRightKanExtension P]
variable [∀ n, ∀ P : (F.obj (op n))ᵒᵖ ⥤ Type w,
    (ι F (op n) ⋙ Grothendieck.map f.toSimplicial).op.HasPointwiseRightKanExtension P]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F J O n).structureMap).IsRightAdjoint]
variable [∀ n, (SheafOfModules.restrictScalars.{w}
    (fiberStageMorphism F' J' O' n).structureMap).IsRightAdjoint]
variable [UnivLE.{max u v, w}]
variable [HasModulePushforwardDerived (Grothendieck.RingedMorphism.toToposHom f)]
variable [∀ n, HasModulePushforwardDerived (Grothendieck.RingedMorphism.topos f n)]

/- Lemma 85.7.3 (2)
In Situation 85.3.3 case B, restriction to each stage commutes
with unbounded derived direct image of modules. -/
@[stacks 0DH1] #check
  (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_hom_isIso f :
    ∀ (n : SimplexCategory),
      IsIso (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_hom f n))

#check (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_hom f :
  ∀ (n : SimplexCategory),
    modulePushforwardDerived (Grothendieck.RingedMorphism.toToposHom f) ⋙
        Grothendieck.derivedModuleRestrict F' J' O' n ⟶
      Grothendieck.derivedModuleRestrict F J O n ⋙
        modulePushforwardDerived (Grothendieck.RingedMorphism.topos f n))

#check (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_obj_isIso f :
  ∀ (n : SimplexCategory) (K : Hom.ModuleDerived.{w} (fiberTotalRingedSite F J O)),
    IsIso (CategoryTheory.Grothendieck.RingedMorphism.restrict_modulePushforwardDerived_obj f n K))

end
