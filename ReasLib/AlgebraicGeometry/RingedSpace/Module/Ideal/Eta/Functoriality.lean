module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta

/-!
# Functoriality of the ideal-sheaf eta complex

The kernel-cokernel construction of `IdealSheaf.Eta.complex` is natural in the input complex.
This file exposes the degreewise maps and packages them as a functor on the canonical full
subcategory `IdealSheaf.Eta.Domain I`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IdealSheaf.Eta

variable {X : RingedSpace.{u}}
variable (I : Subobject (SheafOfModules.unit X.ringCatSheaf : X.Modules))
variable [isInvertibleObject (I : X.Modules)]
variable {K L M : CochainComplex X.Modules ℤ}

/-- The map `I^⊗ i ⊗ K^j ⟶ I^⊗ i ⊗ L^j` induced by a cochain map `φ : K ⟶ L`. -/
noncomputable def tensorTermMap (φ : K ⟶ L) (i j : ℤ) :
    tensorTerm I K i j ⟶ tensorTerm I L i j :=
  tensorHom (𝟙 ((I : X.Modules) ^⊗ i)) (φ.f j)

/-- The ambient differentials in the eta construction are natural in the input complex. -/
theorem ambientDifferential_naturality (φ : K ⟶ L) (i : ℤ) :
    ambientDifferential I K i ≫ tensorTermMap I φ i (i + 1) =
      tensorTermMap I φ i i ≫ ambientDifferential I L i := sorry

/-- The inclusions of successive tensor powers are natural in the input complex. -/
theorem succInclusion_naturality (φ : K ⟶ L) (i : ℤ) :
    succInclusion I K i ≫ tensorTermMap I φ i (i + 1) =
      tensorTermMap I φ (i + 1) (i + 1) ≫ succInclusion I L i := sorry

/-- The map between the quotient targets defining the eta terms. -/
noncomputable def quotientMap (φ : K ⟶ L) (i : ℤ) :
    quotient I K i ⟶ quotient I L i :=
  cokernel.map (succInclusion I K i) (succInclusion I L i)
    (tensorTermMap I φ (i + 1) (i + 1)) (tensorTermMap I φ i (i + 1))
    (succInclusion_naturality I φ i)

/-- The maps to the quotient targets are natural in the input complex. -/
theorem toQuotient_naturality (φ : K ⟶ L) (i : ℤ) :
    toQuotient I K i ≫ quotientMap I φ i =
      tensorTermMap I φ i i ≫ toQuotient I L i := sorry

/-- The degree-`i` map between eta terms induced by a cochain map. -/
noncomputable def objMap (φ : K ⟶ L) (i : ℤ) : obj I K i ⟶ obj I L i :=
  kernel.map (toQuotient I K i) (toQuotient I L i) (tensorTermMap I φ i i)
    (quotientMap I φ i) (toQuotient_naturality I φ i)

/-- The induced maps on eta terms commute with the eta differentials. -/
theorem objMap_naturality [IsActionMono.Complex I K] [IsActionMono.Complex I L]
    (φ : K ⟶ L) (i j : ℤ) (hij : (up ℤ).Rel i j) :
    objMap I φ i ≫ (complex I L).d i j =
      (complex I K).d i j ≫ objMap I φ j := sorry

/-- The morphism of eta complexes induced by a cochain map. -/
noncomputable def map [IsActionMono.Complex I K] [IsActionMono.Complex I L]
    (φ : K ⟶ L) : complex I K ⟶ complex I L where
  f i := objMap I φ i
  comm' i j hij := objMap_naturality I φ i j hij

/-- The eta construction sends identity maps to identity maps. -/
@[simp]
theorem map_id [IsActionMono.Complex I K] : map I (𝟙 K) = 𝟙 (complex I K) := sorry

/-- The eta construction preserves composition of cochain maps. -/
@[simp]
theorem map_comp [IsActionMono.Complex I K] [IsActionMono.Complex I L]
    [IsActionMono.Complex I M] (φ : K ⟶ L) (ψ : L ⟶ M) :
    map I (φ ≫ ψ) = map I φ ≫ map I ψ := sorry

/-- The ideal-sheaf eta construction as a functor on complexes with monic ideal action. -/
noncomputable def functor : Domain I ⥤ CochainComplex X.Modules ℤ where
  obj K := complex I K.obj
  map φ := map I φ.hom
  map_id _ := map_id I
  map_comp φ ψ := map_comp I φ.hom ψ.hom

/-- The object part of the eta functor is the eta complex of the underlying complex. -/
@[simp]
theorem functor_obj (K : Domain I) : (functor I).obj K = complex I K.obj := sorry

/-- The morphism part of the eta functor is the canonical map of eta complexes. -/
@[simp]
theorem functor_map {K L : Domain I} (φ : K ⟶ L) :
    (functor I).map φ = map I φ.hom := sorry

end AlgebraicGeometry.RingedSpace.IdealSheaf.Eta
