module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.Algebra.Module.Flat.Relative
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.HigherDirectImage
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.ModuleProRealization
public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Depth
public import ReasLib.AlgebraicGeometry.Scheme.InfinitesimalFiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Rank
public import ReasLib.RingTheory.Completion.LocalRing

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- The stage of a coherent formal module pulled back to the open infinitesimal fibre. -/
noncomputable def onInfinitesimalFiber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F : CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl))) (n : ℕ+) :
    (Scheme.Opens.toScheme (InfinitesimalFiber.openComplement f Z n)).Modules :=
  (Scheme.Modules.pullback
    (AlgebraicGeometry.morphismRestrict (InfinitesimalFiber.inclusion f n) Z.compl)).obj
      (((F.obj).obj (op (n : ℕ))).obj)

/-- Pulling a formal stage back to the open infinitesimal fibre and pushing it forward recovers
the original formal stage on the complement. -/
theorem pushforward_onInfinitesimalFiber_isIsomorphic
    {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (Z : Closeds X)
    (F : CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl))) (n : ℕ+) :
    IsIsomorphic ((Scheme.Modules.pushforward
      (AlgebraicGeometry.morphismRestrict (InfinitesimalFiber.inclusion f n) Z.compl)).obj
        (onInfinitesimalFiber f Z F n))
      (((F.obj).obj (op (n : ℕ))).obj) := sorry

/-- A quotient-flat coherent formal module with coherent first direct images canonically extends
to the ambient scheme. -/
theorem canonicallyExtends_of_proper_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Z : Closeds X)
    (hZ : (Z : Set X) ⊆
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
    (F : CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl)))
    (h_flat : ∀ n : ℕ+, ∀ x : InfinitesimalFiber.openComplement f Z n,
      Module.FlatAlong ((Scheme.Opens.ι (InfinitesimalFiber.openComplement f Z n) ≫
          InfinitesimalFiber.toSpec f n).stalkMap x).hom
        (RingedSpace.stalkModuleCat (onInfinitesimalFiber f Z F n) x))
    (h_pushforward :
      ((Scheme.Modules.pushforward (Scheme.Opens.ι Z.compl)).obj
        (((F.obj).obj (op 1)).obj)).IsCoherent)
    (h_higherDirectImage :
      (RingedSpace.Hom.higherDirectImageModule (Scheme.Opens.ι Z.compl).toShHom
        (((F.obj).obj (op 1)).obj) 1).IsCoherent) :
    CanonicallyExtendsTo
      ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f)
      (pushforwardProObject Z.compl F) := sorry

/-- A proper-flat quotient-flat formal module admits an ambient coherent algebraization whose
completion restricts to it and realizes the canonical ambient pro-object. -/
theorem exists_global_algebraization_of_proper_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Z : Closeds X)
    (hZ : (Z : Set X) ⊆
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
    (F : CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl)))
    (h_flat : ∀ n : ℕ+, ∀ x : InfinitesimalFiber.openComplement f Z n,
      Module.FlatAlong ((Scheme.Opens.ι (InfinitesimalFiber.openComplement f Z n) ≫
          InfinitesimalFiber.toSpec f n).stalkMap x).hom
        (RingedSpace.stalkModuleCat (onInfinitesimalFiber f Z F n) x))
    (h_pushforward :
      ((Scheme.Modules.pushforward (Scheme.Opens.ι Z.compl)).obj
        (((F.obj).obj (op 1)).obj)).IsCoherent)
    (h_higherDirectImage :
      (RingedSpace.Hom.higherDirectImageModule (Scheme.Opens.ι Z.compl).toShHom
        (((F.obj).obj (op 1)).obj) 1).IsCoherent) :
    ∃ G : RingedSpace.Coh X.toRingedSpace,
      Nonempty ((coherentFormalModulesRestrictionFunctor
        ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f) Z.compl).obj
          ((CoherentCompletion.functor
            ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f)).obj G) ≅ F) ∧
      Nonempty ((moduleProFunctor
        ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f)).obj
          ((CoherentCompletion.functor
            ((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f)).obj G) ≅
        pushforwardProObject Z.compl F) := sorry

/-- Under properness and quotient-flatness, coherence of the first two direct images makes a
formal module the completion of a coherent module on the open complement. -/
theorem isCompletion_of_proper_flat
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Z : Closeds X)
    (hZ : (Z : Set X) ⊆
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
    (F : CoherentFormalModules (Scheme.Opens.toScheme Z.compl)
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl)))
    (h_flat : ∀ n : ℕ+, ∀ x : InfinitesimalFiber.openComplement f Z n,
      Module.FlatAlong ((Scheme.Opens.ι (InfinitesimalFiber.openComplement f Z n) ≫
          InfinitesimalFiber.toSpec f n).stalkMap x).hom
        (RingedSpace.stalkModuleCat (onInfinitesimalFiber f Z F n) x))
    (h_pushforward :
      ((Scheme.Modules.pushforward (Scheme.Opens.ι Z.compl)).obj
        (((F.obj).obj (op 1)).obj)).IsCoherent)
    (h_higherDirectImage :
      (RingedSpace.Hom.higherDirectImageModule (Scheme.Opens.ι Z.compl).toShHom
        (((F.obj).obj (op 1)).obj) 1).IsCoherent) :
    (CoherentCompletion.functor
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).comap
        (Scheme.Opens.ι Z.compl))).essImage F := sorry

/-- On an `(S₂)` irreducible first infinitesimal fibre, codimension at least three and local
freeness imply coherence of the direct image from the open complement. -/
theorem firstStage_pushforward_isCoherent
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Z : Closeds X)
    (hZ : (Z : Set X) ⊆
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
    (hS₂ : satisfiesSerreConditionS (InfinitesimalFiber.stage f 1) 2)
    [IrreducibleSpace (InfinitesimalFiber.stage f 1)]
    (h_dim : topologicalKrullDim
        (InfinitesimalFiber.closedSubset f Z 1 : Set (InfinitesimalFiber.stage f 1)) + 3 ≤
      topologicalKrullDim (InfinitesimalFiber.stage f 1))
    (F₁ : (Scheme.Opens.toScheme (InfinitesimalFiber.openComplement f Z 1)).Modules)
    [F₁.IsCoherent] [F₁.IsFiniteLocallyFree] :
    ((Scheme.Modules.pushforward
      (Scheme.Opens.ι (InfinitesimalFiber.openComplement f Z 1))).obj F₁).IsCoherent := sorry

/-- On an `(S₂)` irreducible first infinitesimal fibre, codimension at least three and local
freeness imply coherence of the degree-one higher direct image. -/
theorem firstStage_higherDirectImage_isCoherent
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsCompleteLocalRing R]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (Z : Closeds X)
    (hZ : (Z : Set X) ⊆
      (((Scheme.idealSheafDataOfIdealOnSpec (IsLocalRing.maximalIdeal R)).comap f).support : Set X))
    (hS₂ : satisfiesSerreConditionS (InfinitesimalFiber.stage f 1) 2)
    [IrreducibleSpace (InfinitesimalFiber.stage f 1)]
    (h_dim : topologicalKrullDim
        (InfinitesimalFiber.closedSubset f Z 1 : Set (InfinitesimalFiber.stage f 1)) + 3 ≤
      topologicalKrullDim (InfinitesimalFiber.stage f 1))
    (F₁ : (Scheme.Opens.toScheme (InfinitesimalFiber.openComplement f Z 1)).Modules)
    [F₁.IsCoherent] [F₁.IsFiniteLocallyFree] :
    (RingedSpace.Hom.higherDirectImageModule
      (Scheme.Opens.ι (InfinitesimalFiber.openComplement f Z 1)).toShHom F₁ 1).IsCoherent := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
