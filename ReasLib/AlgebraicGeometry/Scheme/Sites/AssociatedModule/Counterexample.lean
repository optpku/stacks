/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Properties
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.OverSections
public import ReasLib.CategoryTheory.Linear.PrincipalPower

/-!
# Counterexamples for associated-module functors on big sites

The explicit module `Coker(2 : 𝒪 ⟶ 𝒪)` on `Spec ℤ` witnesses failures of
exactness and internal-Hom preservation for big standard sites.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The quasi-coherent module `Coker(2 : 𝒪 ⟶ 𝒪)` on `Spec ℤ`. -/
noncomputable def twoCokernelModule :
    Scheme.QCoh (Spec (CommRingCat.of ℤ)) :=
  cokernel (2 • 𝟙 (structureModule (Spec (CommRingCat.of ℤ))))

/-- The named two-torsion module is the cokernel of multiplication by `2` on
the structure module of `Spec ℤ`. -/
theorem twoCokernelModule_def :
    twoCokernelModule =
      cokernel (2 • 𝟙 (structureModule (Spec (CommRingCat.of ℤ)))) := sorry

/-- The module `Coker(2 : 𝒪 ⟶ 𝒪)` on `Spec ℤ` is finitely presented. -/
theorem twoCokernelModuleIsFinitePresentation :
    twoCokernelModule.obj.IsFinitePresentation := sorry

/-- The associated big-site module of `Coker(2 : 𝒪 ⟶ 𝒪)` is finitely
presented for every standard topology. -/
@[instance]
theorem twoCokernelBigIsFinitePresentation (τ : StandardTopology) :
    ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
      twoCokernelModule).IsFinitePresentation := sorry

/-- The two-torsion object of the lifted associated structure module is the
kernel of multiplication by `2`. -/
noncomputable abbrev bigStructureModuleTwoTorsion (τ : StandardTopology) :=
  CategoryTheory.Linear.PrincipalPower.kernelStage (2 : ℤ)
    ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
      ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
        (structureModule (Spec (CommRingCat.of ℤ))))) 0

set_option maxHeartbeats 800000 in
/-- Evaluation on the image of the unit gives the canonical comparison from
the internal Hom out of `Coker(2)` to the kernel of multiplication by `2`. -/
noncomputable def twoCokernelInternalHomToTwoTorsion (τ : StandardTopology) :
    (ihom ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
      ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
        twoCokernelModule))).obj
        ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
          ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
            (structureModule (Spec (CommRingCat.of ℤ))))) ⟶
      bigStructureModuleTwoTorsion τ := by
  let S := Spec (CommRingCat.of ℤ)
  let A := (bigModuleLift S τ).obj
    ((bigModuleFunctor S τ).obj (structureModule S))
  let B := (bigModuleLift S τ).obj
    ((bigModuleFunctor S τ).obj twoCokernelModule)
  let unitSection : A.sections :=
    (PresheafOfModules.overSectionsEquivEvaluation A.val).symm
      (ULift.up ((SheafOfModules.sectionsMap
        (Scheme.Modules.pullbackUnitIso (𝟙 S)).inv
        (SheafOfModules.sectionsMap
          (AlgebraicGeometry.RingedSpace.unitIsoTensorUnit S.toRingedSpace).hom
          ((SheafOfModules.unit S.toRingedSpace.ringCatSheaf).unitHomEquiv
            (𝟙 _)))).1 (Opposite.op ⊤)))
  let unitMap : 𝟙_ ((bigCommRingedSite τ S).ModuleCat) ⟶ A :=
    SheafOfModules.RingedSite.tensorUnitToUnitModule
        (J := τ.overTopology S) (𝒪 := bigCommStructureSheaf τ S) ≫
      A.unitHomEquiv.symm unitSection
  let projection : A ⟶ B :=
    (bigModuleLift S τ).map ((bigModuleFunctor S τ).map
      (cokernel.π (2 • 𝟙 (structureModule S)) ≫
        eqToHom (show cokernel (2 • 𝟙 (structureModule S)) =
          twoCokernelModule from rfl)))
  let directEvaluation : (ihom B).obj A ⟶ A :=
    (λ_ _).inv ≫ (unitMap ≫ projection) ▷ _ ≫ (ihom.ev _).app _
  let evaluation : (ihom B).obj A ⟶ A :=
    (MonoidalClosed.pre projection).app A ≫
      (λ_ _).inv ≫ unitMap ▷ _ ≫ (ihom.ev _).app _
  have liftMapAdd : ∀
      {M N : SheafOfModules (bigStructureSheaf τ S)} (f g : M ⟶ N),
      (bigModuleLift S τ).map (f + g) =
        (bigModuleLift S τ).map f + (bigModuleLift S τ).map g := by
    intro M N f g
    change bigModuleLiftMap S τ (f + g) =
      bigModuleLiftMap S τ f + bigModuleLiftMap S τ g
    ext U x
    apply ULift.ext
    change ((f + g).val.app U) x.down =
      f.val.app U x.down + g.val.app U x.down
    rfl
  have liftMapZero : ∀
      {M N : SheafOfModules (bigStructureSheaf τ S)},
      (bigModuleLift S τ).map (0 : M ⟶ N) = 0 := by
    intro M N
    change bigModuleLiftMap S τ (0 : M ⟶ N) = 0
    ext U x
    apply ULift.ext
    rfl
  have functorMapAdd : ∀ {M N : Scheme.QCoh S} (f g : M ⟶ N),
      (bigModuleFunctor S τ).map (f + g) =
        (bigModuleFunctor S τ).map f + (bigModuleFunctor S τ).map g := by
    intro M N f g
    change ((bigFunctor τ S).map (f + g)).hom =
      ((bigFunctor τ S).map f).hom + ((bigFunctor τ S).map g).hom
    ext U x
    change (((Scheme.Modules.pullbackSectionsFunctor (Functor.id _)).map
      ((f + g).hom)).app U) x =
        (((Scheme.Modules.pullbackSectionsFunctor (Functor.id _)).map f.hom).app U) x +
          (((Scheme.Modules.pullbackSectionsFunctor (Functor.id _)).map g.hom).app U) x
    rw [Scheme.Modules.pullbackSectionsFunctor_map_app,
      Scheme.Modules.pullbackSectionsFunctor_map_app,
      Scheme.Modules.pullbackSectionsFunctor_map_app]
    change (((U.unop.left.toRingedSpace.moduleGlobalSectionsFunctor).map
      ((Scheme.Modules.pullback U.unop.hom).map (f.hom + g.hom))) x) = _
    rw [Functor.map_add]
    rfl
  have functorMapZero : ∀ {M N : Scheme.QCoh S},
      (bigModuleFunctor S τ).map (0 : M ⟶ N) = 0 := by
    intro M N
    change ((bigFunctor τ S).map (0 : M ⟶ N)).hom = 0
    ext U x
    change (((Scheme.Modules.pullbackSectionsFunctor (Functor.id _)).map
      ((0 : M ⟶ N).hom)).app U) x = 0
    rw [Scheme.Modules.pullbackSectionsFunctor_map_app]
    change (((U.unop.left.toRingedSpace.moduleGlobalSectionsFunctor).map
      ((Scheme.Modules.pullback U.unop.hom).map (0 : M.obj ⟶ N.obj))) x) = 0
    rw [Functor.map_zero]
    rfl
  have projectionTwoZero : ((2 : ℤ) • 𝟙 A) ≫ projection = 0 := by
    rw [Preadditive.zsmul_comp, Category.id_comp]
    dsimp only [projection]
    rw [two_zsmul, ← liftMapAdd, ← functorMapAdd]
    have hπ :
        (cokernel.π (2 • 𝟙 (structureModule S)) ≫
            eqToHom (show cokernel (2 • 𝟙 (structureModule S)) =
              twoCokernelModule from rfl)) +
          (cokernel.π (2 • 𝟙 (structureModule S)) ≫
            eqToHom (show cokernel (2 • 𝟙 (structureModule S)) =
              twoCokernelModule from rfl)) = 0 := by
      rw [← Preadditive.add_comp, ← two_zsmul]
      calc
        ((2 : ℤ) • cokernel.π (2 • 𝟙 (structureModule S))) ≫
            eqToHom (show cokernel (2 • 𝟙 (structureModule S)) =
              twoCokernelModule from rfl) =
          ((2 • 𝟙 (structureModule S)) ≫
            cokernel.π (2 • 𝟙 (structureModule S))) ≫
              eqToHom (show cokernel (2 • 𝟙 (structureModule S)) =
                twoCokernelModule from rfl) := by
                  simp only [two_zsmul, two_nsmul, Preadditive.add_comp,
                    Category.id_comp]
        _ = 0 := by rw [cokernel.condition, zero_comp]
    rw [hπ, functorMapZero, liftMapZero]
  have directEvaluationTwoZero :
      directEvaluation ≫ ((2 : ℤ) • 𝟙 A) = 0 := by
    dsimp only [directEvaluation]
    rw [Preadditive.comp_zsmul, Category.comp_id, two_zsmul]
    simp only [← Category.assoc]
    rw [← Preadditive.add_comp, ← Preadditive.comp_add,
      ← MonoidalPreadditive.add_whiskerRight, ← two_zsmul]
    rw [show (2 : ℤ) • (unitMap ≫ projection) = 0 by
      rw [← Preadditive.comp_zsmul]
      rw [show (2 : ℤ) • projection = ((2 : ℤ) • 𝟙 _) ≫ projection by
        simp only [Preadditive.zsmul_comp, Category.id_comp]]
      rw [projectionTwoZero, comp_zero]]
    simp
  have directEvaluation_eq_evaluation : directEvaluation = evaluation := by
    dsimp only [directEvaluation, evaluation]
    set_option backward.isDefEq.respectTransparency false in
      symm
      slice_lhs 1 2 => rw [leftUnitor_inv_naturality]
      slice_lhs 2 3 => rw [whisker_exchange]
      slice_lhs 3 4 => rw [MonoidalClosed.id_tensor_pre_app_comp_ev]
      slice_lhs 2 3 => rw [← comp_whiskerRight]
  have evaluationTwoZero : evaluation ≫ ((2 : ℤ) • 𝟙 A) = 0 := by
    rw [← directEvaluation_eq_evaluation]
    exact directEvaluationTwoZero
  exact kernel.lift
    (CategoryTheory.Linear.PrincipalPower.smulPow (2 : ℤ) A 1)
    evaluation
    (by simpa only [CategoryTheory.Linear.PrincipalPower.smulPow, pow_one] using
      evaluationTwoZero)

/-- The canonical comparison from the internal Hom out of `Coker(2)` to the
two-torsion object is invertible. -/
@[instance]
theorem twoCokernelInternalHomToTwoTorsionIsIso (τ : StandardTopology) :
    IsIso (twoCokernelInternalHomToTwoTorsion τ) := sorry

/-- The two-torsion in the lifted associated structure module on the big
standard site of `Spec ℤ` is not quasicoherent. -/
theorem bigStructureModuleTwoTorsionNotQuasicoherent
    (τ : StandardTopology) :
    ¬ (bigStructureModuleTwoTorsion τ).IsQuasicoherent := sorry

/-- The internal Hom from the lifted associated module `Coker(2)` to the
lifted associated structure module is not quasicoherent. -/
theorem twoCokernelInternalHomNotQuasicoherent (τ : StandardTopology) :
    ¬ ((ihom ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
        ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
          twoCokernelModule))).obj
      ((bigModuleLift (Spec (CommRingCat.of ℤ)) τ).obj
        ((bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ).obj
          (structureModule (Spec (CommRingCat.of ℤ)))))).IsQuasicoherent := sorry

/-- On `Spec ℤ`, the associated-module functor to any big standard site is not
exact. -/
theorem bigModuleFunctorNotExact (τ : StandardTopology) :
    ¬ exactFunctor (Scheme.QCoh (Spec (CommRingCat.of ℤ)))
      (SheafOfModules (bigStructureSheaf τ (Spec (CommRingCat.of ℤ))))
      (bigModuleFunctor (Spec (CommRingCat.of ℤ)) τ) := sorry

/-- On `Spec ℤ`, the canonical big-site internal-Hom comparison fails for the
finitely presented module `Coker(2 : 𝒪 ⟶ 𝒪)` against the structure module. -/
theorem bigInternalHomNotPreserved (τ : StandardTopology) :
    ¬ IsIso (bigModuleInternalHomComparison (Spec (CommRingCat.of ℤ)) τ
      twoCokernelModule (structureModule (Spec (CommRingCat.of ℤ)))
      twoCokernelModuleIsFinitePresentation) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
