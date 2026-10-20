/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.BerthelotOgus.Eta.Int
public import ReasLib.Algebra.Homology.HomologicalComplex.CanonicalRows
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal
public import ReasLib.RingTheory.Ideal.Principal
public import Mathlib.Algebra.Category.ModuleCat.Images

/-!
# Reduction of the integer-indexed Berthelot-Ogus eta complex

For the divided-differential model `Int.eta f K hK`, an element in degree `i` is already an
element `x : K.X i` whose differential is divisible by `f`.  Its reduction modulo `(f)` is
therefore canonically a cycle of `K / fK`.  This construction works uniformly in every integer
degree and does not use a natural-number truncation or degree-dependent powers of `f`.

The quotient complexes are supplied by `HomologicalComplex.ModIdeal`.  This file adds only the
eta-specific inclusion into the ambient complex, its factorization through cycles and homology,
and the boundary presentation from the source remark.

@stack 0F7S
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
open scoped nonZeroDivisors

noncomputable section

universe u v

namespace CochainComplex.BerthelotOgus.Int.Reduction

variable {A : Type u} [CommRing A]

/-- The reduction of an integer-indexed cochain complex modulo the principal ideal `(f)`. -/
@[stacks 0F7S "ambient quotient complex for eta reduction"]
def ambientComplex (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) :
    CochainComplex (ModuleCat.{v} (A ⧸ principalIdeal f)) ℤ :=
  HomologicalComplex.ModIdeal.complex (principalIdeal f) K

/-- The morphism of ambient quotient complexes induced by a cochain map. -/
@[stacks 0F7S "map of ambient quotient complexes"]
def ambientMap (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) :
    ambientComplex f K ⟶ ambientComplex f L :=
  HomologicalComplex.ModIdeal.map (principalIdeal f) φ

/-- The termwise reduction of the integer-indexed divided-differential eta complex modulo
`f`. -/
@[stacks 0F7S "reduction of the integer-indexed Berthelot-Ogus eta complex"]
def complex (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    CochainComplex (ModuleCat.{v} (A ⧸ principalIdeal f)) ℤ :=
  HomologicalComplex.ModIdeal.complex (principalIdeal f) (eta f K hK)

/-- The morphism of reduced eta complexes induced by a cochain map between torsion-free
complexes. -/
@[stacks 0F7S "map of reduced integer eta complexes"]
def map (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L)
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L) :
    complex f K hK ⟶ complex f L hL :=
  HomologicalComplex.ModIdeal.map (principalIdeal f) (Int.map f φ hK hL)

/-- Integer-indexed eta reduction sends identity morphisms to identity morphisms. -/
@[simp]
theorem map_id (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    map f (𝟙 K) hK hK = 𝟙 (complex f K hK) := sorry

/-- Integer-indexed eta reduction preserves composition. -/
@[simp]
theorem map_comp (f : A) {K L M : CochainComplex (ModuleCat.{v} A) ℤ}
    (φ : K ⟶ L) (ψ : L ⟶ M) (hK : IsTermwiseTorsionFree f K)
    (hL : IsTermwiseTorsionFree f L) (hM : IsTermwiseTorsionFree f M) :
    map f (φ ≫ ψ) hK hM = map f φ hK hL ≫ map f ψ hL hM := sorry

/-- The functorial reduction of the divided-differential eta construction on its canonical
torsion-free domain. -/
@[stacks 0F7S "functorial integer-indexed eta reduction"]
def functor (f : A) :
    Int.Domain f ⥤ CochainComplex (ModuleCat.{v} (A ⧸ principalIdeal f)) ℤ where
  obj K := complex f K.obj K.property
  map {K L} φ := map f φ.hom K.property L.property
  map_id K := map_id f K.obj K.property
  map_comp {K L M} φ ψ :=
    map_comp f φ.hom ψ.hom K.property L.property M.property

/-- The divided-differential eta term includes canonically into the corresponding term of the
ambient complex. -/
@[stacks 0F7S "eta-term inclusion into the ambient complex"]
def inclusionLinear (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    term f K i →ₗ[A] K.X i :=
  (term f K i).subtype

/-- Reduction modulo `(f)` of the canonical inclusion of an eta term into its ambient term. -/
@[stacks 0F7S "reduced eta-term inclusion"]
noncomputable def quotientLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i →ₗ[A ⧸ principalIdeal f] (ambientComplex f K).X i :=
  LinearMap.IdealQuotient.map (inclusionLinear f K i) (principalIdeal f)

/-- On a quotient generator, `quotientLinear` is represented by the underlying eta-term
element itself. -/
theorem quotientLinear_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (x : term f K i) :
    quotientLinear f K i hK (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((inclusionLinear f K i) x) := sorry

/-- The reduced inclusion regarded as a morphism of quotient-ring modules. -/
@[stacks 0F7S "bundled reduced eta-term inclusion"]
noncomputable def quotientHom
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i ⟶ (ambientComplex f K).X i :=
  ModuleCat.ofHom (quotientLinear f K i hK)

/-- The reduced inclusions commute with maps of torsion-free complexes. -/
theorem quotientHom_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L) :
    (map f φ hK hL).f i ≫ quotientHom f L i hL =
      quotientHom f K i hK ≫ (ambientMap f φ).f i := sorry

/-- The reduced inclusion has zero composite with the next ambient differential because the
differential of every divided eta term is a multiple of `f`. -/
theorem quotientHom_comp_d
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    quotientHom f K i hK ≫ (ambientComplex f K).d i (i + 1) = 0 := sorry

/-- Consecutive integer degrees satisfy the cochain-complex relation. -/
theorem rel_succ (i : ℤ) : (ComplexShape.up ℤ).Rel i (i + 1) := sorry

/-- Remark 15.96.5, tag `0F7S` (1): reduction of the canonical inclusion induces
`(complex f K hK).X i ⟶ (ambientComplex f K).cycles i` in every integer degree. -/
@[stacks 0F7S "integer-indexed eta reduction maps to cycles modulo f"]
noncomputable def toCycles
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i ⟶ (ambientComplex f K).cycles i :=
  (ambientComplex f K).liftCycles' (quotientHom f K i hK)
    (i + 1) (rel_succ i) (quotientHom_comp_d f K i hK)

/-- The canonical comparison
`(complex f K hK).X i ⟶ (ambientComplex f K).homology i`. -/
@[stacks 0F7S "integer-indexed eta reduction maps to homology modulo f"]
noncomputable def toHomology
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (complex f K hK).X i ⟶ (ambientComplex f K).homology i :=
  toCycles f K i hK ≫ (ambientComplex f K).homologyπ i

/-- The comparison with ambient cycles is natural in the torsion-free complex. -/
theorem toCycles_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L) :
    (map f φ hK hL).f i ≫ toCycles f L i hL =
      toCycles f K i hK ≫ HomologicalComplex.cyclesMap (ambientMap f φ) i := sorry

/-- The comparison with ambient homology is natural in the torsion-free complex. -/
theorem toHomology_naturality
    (f : A) {K L : CochainComplex (ModuleCat.{v} A) ℤ} (φ : K ⟶ L) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (hL : IsTermwiseTorsionFree f L) :
    (map f φ hK hL).f i ≫ toHomology f L i hL =
      toHomology f K i hK ≫ HomologicalComplex.homologyMap (ambientMap f φ) i := sorry

/-- Multiplication by `f` sends every ambient degree-`i` term into the corresponding eta
term. -/
theorem mul_mem_term
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) (x : K.X i) :
    f • x ∈ term f K i := sorry

/-- Multiplication by `f`, with codomain restricted to the degree-`i` eta term. -/
@[stacks 0F7S "multiplication into an eta term"]
def mulIntoTermLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    K.X i →ₗ[A] term f K i :=
  (LinearMap.lsmul A (K.X i) f).codRestrict (term f K i) (mul_mem_term f K i)

/-- The quotient map underlying the source map `s` before it is restricted to outgoing
boundaries. -/
@[stacks 0F7S "auxiliary outgoing-boundary map"]
noncomputable def boundaryAuxLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (ambientComplex f K).X i →ₗ[A ⧸ principalIdeal f] (complex f K hK).X i :=
  LinearMap.IdealQuotient.map (mulIntoTermLinear f K i) (principalIdeal f)

/-- On quotient generators, `boundaryAuxLinear` is represented by multiplication by `f`. -/
theorem boundaryAuxLinear_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) (x : K.X i) :
    boundaryAuxLinear f K i hK (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk ((mulIntoTermLinear f K i) x) := sorry

/-- The quotient map defining `s` vanishes on the kernel of the outgoing reduced
differential. -/
theorem outgoing_ker_le_boundaryAux_ker
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    ((ambientComplex f K).d i (i + 1)).hom.ker ≤
      (boundaryAuxLinear f K i hK).ker := sorry

/-- The linear map from the range of the outgoing reduced differential induced by
`boundaryAuxLinear`. -/
@[stacks 0F7S "map from outgoing reduced boundaries"]
noncomputable def boundaryRangeLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    LinearMap.range ((ambientComplex f K).d i (i + 1)).hom
        →ₗ[A ⧸ principalIdeal f] (complex f K hK).X i :=
  (((ambientComplex f K).d i (i + 1)).hom.ker.liftQ
      (boundaryAuxLinear f K i hK)
      (outgoing_ker_le_boundaryAux_ker f K i hK)).comp
    ((ambientComplex f K).d i (i + 1)).hom.quotKerEquivRange.symm.toLinearMap

/-- Remark 15.96.5, tag `0F7S` (2): the map `s` from outgoing boundaries to the
reduced eta term, obtained from the explicit formula `x ↦ f • x`. -/
@[stacks 0F7S "outgoing boundaries map into the reduced eta term"]
noncomputable def boundary
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    image ((ambientComplex f K).d i (i + 1)) ⟶ (complex f K hK).X i :=
  (ModuleCat.imageIsoRange ((ambientComplex f K).d i (i + 1))).hom ≫
    ModuleCat.ofHom (boundaryRangeLinear f K i hK)

/-- Factoring the outgoing reduced differential through its image and then applying `boundary`
recovers the explicit quotient map. -/
theorem factorThruImage_comp_boundary
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    factorThruImage ((ambientComplex f K).d i (i + 1)) ≫ boundary f K i hK =
      ModuleCat.ofHom (boundaryAuxLinear f K i hK) := sorry

/-- The incoming differential in degree `i` has image in the degree-`i` eta term. -/
theorem previousD_mem_term
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (z : K.X ((ComplexShape.up ℤ).prev i)) :
    (K.d ((ComplexShape.up ℤ).prev i) i) z ∈ term f K i := sorry

/-- The incoming differential with codomain restricted to the degree-`i` eta term. -/
@[stacks 0F7S "incoming differential into an eta term"]
def previousDIntoTermLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    K.X ((ComplexShape.up ℤ).prev i) →ₗ[A] term f K i :=
  (K.d ((ComplexShape.up ℤ).prev i) i).hom.codRestrict (term f K i)
    (previousD_mem_term f K i)

/-- The quotient map underlying the source map `s'` before it is restricted to incoming
boundaries. -/
@[stacks 0F7S "auxiliary incoming-boundary map"]
noncomputable def previousBoundaryAuxLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    (ambientComplex f K).X ((ComplexShape.up ℤ).prev i)
        →ₗ[A ⧸ principalIdeal f] (complex f K hK).X i :=
  LinearMap.IdealQuotient.map (previousDIntoTermLinear f K i) (principalIdeal f)

/-- On quotient generators, `previousBoundaryAuxLinear` is represented by the incoming
differential. -/
theorem previousBoundaryAuxLinear_mk
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K)
    (z : K.X ((ComplexShape.up ℤ).prev i)) :
    previousBoundaryAuxLinear f K i hK (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk ((previousDIntoTermLinear f K i) z) := sorry

/-- The quotient map defining `s'` vanishes on the kernel of the incoming reduced
differential. -/
theorem incoming_ker_le_previousBoundaryAux_ker
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i).hom.ker ≤
      (previousBoundaryAuxLinear f K i hK).ker := sorry

/-- The linear map from the range of the incoming reduced differential induced by
`previousBoundaryAuxLinear`. -/
@[stacks 0F7S "map from incoming reduced boundaries"]
noncomputable def previousBoundaryRangeLinear
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    LinearMap.range ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i).hom
        →ₗ[A ⧸ principalIdeal f] (complex f K hK).X i :=
  (((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i).hom.ker.liftQ
      (previousBoundaryAuxLinear f K i hK)
      (incoming_ker_le_previousBoundaryAux_ker f K i hK)).comp
    ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i).hom.quotKerEquivRange.symm.toLinearMap

/-- Remark 15.96.5, tag `0F7S` (3): the map `s'` from incoming boundaries to the
reduced eta term, induced by the incoming differential. -/
@[stacks 0F7S "incoming boundaries map into the reduced eta term"]
noncomputable def previousBoundary
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    image ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i) ⟶
      (complex f K hK).X i :=
  (ModuleCat.imageIsoRange
      ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i)).hom ≫
    ModuleCat.ofHom (previousBoundaryRangeLinear f K i hK)

/-- Factoring the incoming reduced differential through its image and then applying
`previousBoundary` recovers the explicit quotient map. -/
theorem factorThruImage_comp_previousBoundary
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    factorThruImage ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i) ≫
        previousBoundary f K i hK =
      ModuleCat.ofHom (previousBoundaryAuxLinear f K i hK) := sorry

/-- The middle vertical map `(s, s')` in the boundary diagram. -/
@[stacks 0F7S "middle map in the eta boundary diagram"]
noncomputable def boundaryPair
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    image ((ambientComplex f K).d i (i + 1)) ⊞
        image ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i) ⟶
      (complex f K hK).X i :=
  biprod.desc (boundary f K i hK) (previousBoundary f K i hK)

/-- The split upper row of the boundary diagram. -/
@[stacks 0F7S "split row of the eta boundary diagram"]
noncomputable def splitBoundaryShortComplex
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ) :
    ShortComplex (ModuleCat.{v} (A ⧸ principalIdeal f)) :=
  ShortComplex.mk
    (biprod.inl :
      image ((ambientComplex f K).d i (i + 1)) ⟶
        image ((ambientComplex f K).d i (i + 1)) ⊞
          image ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i))
    (biprod.snd :
      image ((ambientComplex f K).d i (i + 1)) ⊞
          image ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i) ⟶
        image ((ambientComplex f K).d ((ComplexShape.up ℤ).prev i) i))
    biprod.inl_snd

/-- The map `boundary` has zero composite with the map to ambient cycles. -/
theorem boundary_comp_toCycles
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    boundary f K i hK ≫ toCycles f K i hK = 0 := sorry

/-- The lower row of the boundary diagram. -/
@[stacks 0F7S "boundary row of the reduced eta diagram"]
noncomputable def boundaryShortComplex
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    ShortComplex (ModuleCat.{v} (A ⧸ principalIdeal f)) :=
  ShortComplex.mk (boundary f K i hK) (toCycles f K i hK)
    (boundary_comp_toCycles f K i hK)

/-- The left square of the boundary diagram commutes. -/
theorem boundaryDiagram_comm_left
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    𝟙 (image ((ambientComplex f K).d i (i + 1))) ≫ boundary f K i hK =
      (splitBoundaryShortComplex f K i).f ≫ boundaryPair f K i hK := sorry

/-- The right square of the boundary diagram commutes. -/
theorem boundaryDiagram_comm_right
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    boundaryPair f K i hK ≫ toCycles f K i hK =
      (splitBoundaryShortComplex f K i).g ≫
        (ambientComplex f K).imageToCycles ((ComplexShape.up ℤ).prev i) i := sorry

/-- The commutative boundary diagram whose middle vertical map is `(s, s')`. -/
@[stacks 0F7S "commutative boundary diagram for eta reduction"]
noncomputable def boundaryDiagram
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hK : IsTermwiseTorsionFree f K) :
    splitBoundaryShortComplex f K i ⟶ boundaryShortComplex f K i hK where
  τ₁ := 𝟙 _
  τ₂ := boundaryPair f K i hK
  τ₃ := (ambientComplex f K).imageToCycles ((ComplexShape.up ℤ).prev i) i
  comm₁₂ := boundaryDiagram_comm_left f K i hK
  comm₂₃ := boundaryDiagram_comm_right f K i hK

/-- Remark 15.96.5, tag `0F7S`: if `f` is a nonzerodivisor and `K` is termwise
`f`-torsion-free, both rows of `boundaryDiagram` are short exact. -/
@[stacks 0F7S "exact boundary diagram for the reduced eta complex"]
theorem boundaryDiagram_hasExactRows
    (f : A) (K : CochainComplex (ModuleCat.{v} A) ℤ) (i : ℤ)
    (hf : f ∈ nonZeroDivisors A) (hK : IsTermwiseTorsionFree f K) :
    (splitBoundaryShortComplex f K i).ShortExact ∧
      (boundaryShortComplex f K i hK).ShortExact := sorry

end CochainComplex.BerthelotOgus.Int.Reduction
