module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap75.Lemma_75_23_3_Comparison

/-!
# Base change of Ext representations on algebraic spaces

A pseudo-coherent object representing Ext against `G ⊗ f^* -` remains a
representation after cartesian base change. The coefficient complex `G` is
pulled back termwise as an ordinary complex, not in the derived category.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory.DerivedCategory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open ComplexShape DerivedCategory.TStructure TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}
variable [MonoidalCategory (ModuleDerived X)]

/-- Termwise tensor of `G` against `f^*` of a short complex of modules. -/
def tensorPullbackShortComplex (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B)) : ShortComplex (CochainComplex (Modules X) ℤ) :=
  ShortComplex.mk
    (HomologicalComplex.tensorHom (𝟙 G)
      ((HomologicalComplex.single (Modules X) (up ℤ) 0).map ((Modules.pullback f).map s.f)))
    (HomologicalComplex.tensorHom (𝟙 G)
      ((HomologicalComplex.single (Modules X) (up ℤ) 0).map ((Modules.pullback f).map s.g)))
    sorry

/-- `G ⊗ f^* s` is short exact when `s` is short exact and each `G^n` is flat over `B`. -/
theorem tensorPullback_shortExact (f : X ⟶ B) (G : CochainComplex (Modules X) ℤ)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (s : ShortComplex (Modules B)) (hs : s.ShortExact) :
    (tensorPullbackShortComplex f G s).ShortExact :=
  sorry

/-- Induced map on `ihom(E, Q(G ⊗ f^* -))` from a morphism of modules on the base. -/
def RepresentsExt.targetMap (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) {F F' : Modules B}
    (φ : F ⟶ F') : extTarget f H E G F ⟶ extTarget f H E G F' :=
  (ihomOf H E).map
    (DerivedCategory.Q.map
      (HomologicalComplex.tensorHom (𝟙 G)
        ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
          ((Modules.pullback f).map φ))))

/-- `RepresentsExt.targetMap` is derived internal Hom of underived tensor with `f^* φ`. -/
theorem RepresentsExt.targetMap_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) {F F' : Modules B}
    (φ : F ⟶ F') :
    RepresentsExt.targetMap f H E G φ =
      (ihomOf H E).map
        (DerivedCategory.Q.map
          (HomologicalComplex.tensorHom (𝟙 G)
            ((HomologicalComplex.single (Modules X) (up ℤ) 0).map
              ((Modules.pullback f).map φ)))) :=
  rfl

/-- Connecting map on `Ext^i_{𝒪_X}(E, G ⊗ f^* -)` attached to a short exact sequence. -/
def RepresentsExt.targetδ (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B))
    (hs : (tensorPullbackShortComplex f G s).ShortExact) (i : ℤ)
    [(ihomOf H E).CommShift ℤ] :
    cohomologyAb X (extTarget f H E G s.X₃) i ⟶
      cohomologyAb X (extTarget f H E G s.X₁) (i + 1) :=
  (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
    ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
      ((ihomOf H E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
    i (i + 1) rfl

/-- `RepresentsExt.targetδ` is homology of the internal-Hom triangle of `G ⊗ f^* s`. -/
theorem RepresentsExt.targetδ_eq (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ)
    (s : ShortComplex (Modules B))
    (hs : (tensorPullbackShortComplex f G s).ShortExact) (i : ℤ)
    [(ihomOf H E).CommShift ℤ] :
    RepresentsExt.targetδ f H E G s hs i =
      (DerivedCategory.homologyFunctor AddCommGrpCat.{u} 0).homologySequenceδ
        ((moduleDerivedGlobalSectionsAb X).mapTriangle.obj
          ((ihomOf H E).mapTriangle.obj (DerivedCategory.triangleOfSES hs)))
        i (i + 1) rfl :=
  rfl

variable [MonoidalCategory (ModuleDerived B)]

/-- A derived module `L` on `B` represents Ext against `G ⊗ f^* -` when some comparison
family identifies `Ext^i_B(L, F)` with `Ext^i_X(E, G ⊗ f^* F)` for quasi-coherent `F`,
naturally in `F` and compatibly with connecting maps. -/
def RepresentsExt (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B) : Prop :=
  ∃ α :
    ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
      cohomologyAb B
          ((ihomOf H_B L).obj ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
        cohomologyAb X (extTarget f H E G F) i,
    (∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
        IsIso (α F hF i)) ∧
      (∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
          (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
          α F hF i ≫ cohomologyAb_map (RepresentsExt.targetMap f H E G φ) i =
            cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i) ∧
        ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
          (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
          (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
          (hF₁ : quasiCoherentModuleProperty B s.X₁)
          (hF₂ : quasiCoherentModuleProperty B s.X₂)
          (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
          [(ihomOf H E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
          α s.X₃ hF₃ i ≫
              RepresentsExt.targetδ f H E G s
                (tensorPullback_shortExact f G hG_flat s hs) i =
            representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1)

/-- Package degreewise isomorphisms, naturality, and boundary compatibility as an
Ext representation. -/
def RepresentsExt.of (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb B
            ((ihomOf H_B L).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
          cohomologyAb X (extTarget f H E G F) i)
    (hIso :
      ∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
        IsIso (α F hF i))
    (hNat :
      ∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
        (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
        α F hF i ≫ cohomologyAb_map (RepresentsExt.targetMap f H E G φ) i =
          cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i)
    (hBoundary :
      ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
        (hs0 : (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
        (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
        (hF₁ : quasiCoherentModuleProperty B s.X₁)
        (hF₂ : quasiCoherentModuleProperty B s.X₂)
        (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
        [(ihomOf H E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
        α s.X₃ hF₃ i ≫
            RepresentsExt.targetδ f H E G s
              (tensorPullback_shortExact f G hG_flat s hs) i =
          representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1)) :
    RepresentsExt f H H_B E G L :=
  ⟨α, hIso, hNat, hBoundary⟩

/-- Representing Ext against `G ⊗ f^* -` means there is a comparison family that is
invertible in every degree, natural in quasi-coherent coefficients, and compatible
with connecting maps. -/
theorem RepresentsExt.iff (f : X ⟶ B) (H : MonoidalClosed (ModuleDerived X))
    (H_B : MonoidalClosed (ModuleDerived B)) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B) :
    RepresentsExt f H H_B E G L ↔
      ∃ α :
        ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
          cohomologyAb B
              ((ihomOf H_B L).obj
                ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
            cohomologyAb X (extTarget f H E G F) i,
        (∀ (F : Modules B) (hF : quasiCoherentModuleProperty B F) (i : ℤ),
            IsIso (α F hF i)) ∧
          (∀ {F F' : Modules B} (φ : F ⟶ F') (hF : quasiCoherentModuleProperty B F)
              (hF' : quasiCoherentModuleProperty B F') (i : ℤ),
              α F hF i ≫ cohomologyAb_map (RepresentsExt.targetMap f H E G φ) i =
                cohomologyAb_map (representedExtMap H_B L φ) i ≫ α F' hF' i) ∧
            ∀ (s : ShortComplex (Modules B)) (hs : s.ShortExact)
              (hs0 :
                (s.map (HomologicalComplex.single (Modules B) (up ℤ) 0)).ShortExact)
              (hG_flat : ∀ (j : ℤ) (x), Modules.flatOverAt (G.X j) f x)
              (hF₁ : quasiCoherentModuleProperty B s.X₁)
              (hF₂ : quasiCoherentModuleProperty B s.X₂)
              (hF₃ : quasiCoherentModuleProperty B s.X₃) (i : ℤ)
              [(ihomOf H E).CommShift ℤ] [(tensorLeft L).CommShift ℤ],
              α s.X₃ hF₃ i ≫
                  RepresentsExt.targetδ f H E G s
                    (tensorPullback_shortExact f G hG_flat s hs) i =
                representedExtδ H_B L s hs0 i ≫ α s.X₁ hF₁ (i + 1) :=
  sorry

/-- A pseudo-coherent Ext-representation certificate forgets to an Ext representation. -/
theorem RepresentsExt.of_isPseudoCoherentExtRepresentation [localizationMonoidal X]
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (H : MonoidalClosed (ModuleDerived X)) (H_B : MonoidalClosed (ModuleDerived B))
    (E : ModuleDerived X) (G : CochainComplex (Modules X) ℤ) (L : ModuleDerived B)
    (α :
      ∀ (F : Modules B) (_ : quasiCoherentModuleProperty B F) (i : ℤ),
        cohomologyAb B
            ((ihomOf H_B L).obj
              ((DerivedCategory.singleFunctor (Modules B) 0).obj F)) i ⟶
          cohomologyAb X (extTarget f H E G F) i)
    (h : IsPseudoCoherentExtRepresentation f H H_B E G L α) :
    RepresentsExt f H H_B E G L :=
  sorry

/-- An explicit pseudo-coherent Ext representation remains a representation after
cartesian base change. The complexes `E` and `L` are pulled back in the derived
category, while `G` is pulled back termwise as an ordinary complex. -/
theorem RepresentsExt.pullback [localizationMonoidal X]
    (f : X ⟶ B) [LocallyOfFiniteType f] [QuasiSeparated f] [IsNoetherian B]
    (H : MonoidalClosed (ModuleDerived X)) (H_B : MonoidalClosed (ModuleDerived B))
    (E : ModuleDerived X)
    (hE_minus : (t.minus : ObjectProperty (ModuleDerived X)) E)
    (hE_coherent :
      DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent (structureSheaf X)) E)
    (G : CochainComplex (Modules X) ℤ)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_coherent : ∀ i : ℤ, (G.X i).IsCoherent)
    (hG_flat : ∀ i : ℤ, ∀ x, Modules.flatOverAt (G.X i) f x)
    (hG_support :
      ∀ i : ℤ,
        ClosedSubset.IsProperOver f
          (Closeds.closure (Modules.moduleSupport (G.X i))))
    (L : ModuleDerived B) (hL : IsPseudoCoherent B L)
    (hrep : RepresentsExt f H H_B E G L)
    {X' Y' : AlgebraicSpace S}
    [MonoidalCategory (ModuleDerived X')] [localizationMonoidal X']
    [MonoidalCategory (ModuleDerived Y')]
    (H' : MonoidalClosed (ModuleDerived X'))
    (H_Y' : MonoidalClosed (ModuleDerived Y'))
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (g : Y' ⟶ B) (sq : IsPullback g' f' f g) :
    RepresentsExt f' H' H_Y' ((modulePullbackDerived g').obj E)
      (((Modules.pullback g').mapHomologicalComplex (up ℤ)).obj G)
      ((modulePullbackDerived g).obj L) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
