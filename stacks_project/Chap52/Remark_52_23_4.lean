/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Algebraization.ProperFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

/- Remark 52.23.4 (1) -/
@[stacks 0EJV] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.isCompletion_of_proper_flat :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
      {X : Scheme.{u}} [IsNoetherian X]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (Z : Closeds X)
      (hZ : (Z : Set X) ⊆
        (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
      (F : Scheme.CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
        (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
          (Scheme.Opens.ι Z.compl)))
      (h_flat : ∀ n : ℕ+, ∀ x : Scheme.InfinitesimalFiber.openComplement f Z n,
        Module.FlatAlong ((Scheme.Opens.ι (Scheme.InfinitesimalFiber.openComplement f Z n) ≫
            Scheme.InfinitesimalFiber.toSpec f n).stalkMap x).hom
          (RingedSpace.stalkModuleCat
            (Scheme.CoherentFormalModules.onInfinitesimalFiber f Z F n) x))
      (h_pushforward :
        ((Scheme.Modules.pushforward (Scheme.Opens.ι Z.compl)).obj
          (((F.obj).obj (op 1)).obj)).IsCoherent)
      (h_higherDirectImage :
        (RingedSpace.Hom.higherDirectImageModule (Scheme.Opens.ι Z.compl).toShHom
          (((F.obj).obj (op 1)).obj) 1).IsCoherent),
      (Scheme.CoherentCompletion.functor
        (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
          (Scheme.Opens.ι Z.compl))).essImage F)
#check AlgebraicGeometry.Scheme.CoherentFormalModules.canonicallyExtends_of_proper_flat
#check AlgebraicGeometry.Scheme.CoherentFormalModules.exists_global_algebraization_of_proper_flat

/- Remark 52.23.4 (2) -/
@[stacks 0EJV] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.firstStage_pushforward_isCoherent :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
      {X : Scheme.{u}} [IsNoetherian X]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (Z : Closeds X)
      (hZ : (Z : Set X) ⊆
        (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
      (hS₂ : Scheme.satisfiesSerreConditionS (Scheme.InfinitesimalFiber.stage f 1) 2)
      [IrreducibleSpace (Scheme.InfinitesimalFiber.stage f 1)]
      (h_dim : topologicalKrullDim
          (Scheme.InfinitesimalFiber.closedSubset f Z 1 : Set (Scheme.InfinitesimalFiber.stage f 1)) + 3 ≤
        topologicalKrullDim (Scheme.InfinitesimalFiber.stage f 1))
      (F₁ : (Scheme.Opens.toScheme (Scheme.InfinitesimalFiber.openComplement f Z 1)).Modules)
      [F₁.IsCoherent] [F₁.IsFiniteLocallyFree],
      ((Scheme.Modules.pushforward
        (Scheme.Opens.ι (Scheme.InfinitesimalFiber.openComplement f Z 1))).obj F₁).IsCoherent)

/- Remark 52.23.4 (3) -/
@[stacks 0EJV] #check (AlgebraicGeometry.Scheme.CoherentFormalModules.firstStage_higherDirectImage_isCoherent :
    ∀ {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
      {X : Scheme.{u}} [IsNoetherian X]
      (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
      (Z : Closeds X)
      (hZ : (Z : Set X) ⊆
        (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
      (hS₂ : Scheme.satisfiesSerreConditionS (Scheme.InfinitesimalFiber.stage f 1) 2)
      [IrreducibleSpace (Scheme.InfinitesimalFiber.stage f 1)]
      (h_dim : topologicalKrullDim
          (Scheme.InfinitesimalFiber.closedSubset f Z 1 : Set (Scheme.InfinitesimalFiber.stage f 1)) + 3 ≤
        topologicalKrullDim (Scheme.InfinitesimalFiber.stage f 1))
      (F₁ : (Scheme.Opens.toScheme (Scheme.InfinitesimalFiber.openComplement f Z 1)).Modules)
      [F₁.IsCoherent] [F₁.IsFiniteLocallyFree],
      (RingedSpace.Hom.higherDirectImageModule
        (Scheme.Opens.ι (Scheme.InfinitesimalFiber.openComplement f Z 1)).toShHom F₁ 1).IsCoherent)
