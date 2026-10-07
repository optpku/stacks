module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Pairing
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CoherentBounded

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.Bounded Scheme.Hom
open DerivedCategory.TStructure
open scoped DerivedCategory.CohomologyIn DerivedExt
open AlgebraicGeometry.Scheme.DerivedQCoh
open AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex

noncomputable section

universe u

/- Remark 48.27.2
The identity of the proper dualizing complex induces a trace pairing
`Extⁱ(K, ω) → Dual(H⁻ⁱ(K))` after an identification of the affine-derived field object
with `k`. -/
@[stacks 0FVW]
#check (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith :
  {k : Type u} → [Field k] → {X : Scheme.{u}} →
  (e : AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.fieldObject k ≅
    ModuleCat.of k k) →
  (f : X ⟶ Spec (CommRingCat.of k)) → [IsProper f] →
  (i : ℤ) → (K : AlgebraicGeometry.Scheme.DerivedQCoh X) →
  DerivedExt.value f K.obj
      (AlgebraicGeometry.Scheme.DerivedQCoh.properDualizingComplex f).obj i →ₗ[k]
    Module.Dual k
      (AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.cohomologyOverField f K (-i)))

#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.traceWith
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_trace
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_bijective
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.boundedCohomologyFinite
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.boundedExtFinite
#check AlgebraicGeometry.Scheme.DerivedQCoh.ProperDualizingComplex.pairingWith_isPerfPair
