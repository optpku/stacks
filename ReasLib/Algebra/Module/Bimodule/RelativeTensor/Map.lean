module

public import ReasLib.Algebra.Module.Bimodule.Hom
public import ReasLib.Algebra.Module.Bimodule.RelativeTensor

/-!
# Functorial Maps on Relative Tensor Products

This file provides the maps induced in either relative tensor factor, their simultaneous
bifunctorial map, evaluation on pure tensors, interchange, identity, and composition laws.
-/

@[expose] public section

noncomputable section

namespace Module.Bimodule

universe i j u v w x y z t

variable {R : Type u} [CommRing R]
variable {A : Type v} [Ring A] [Algebra R A]
variable {B : Type w} [Ring B] [Algebra R B]

namespace RelativeTensor

variable {M : Type x} [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M]
variable [IsScalarTower R Aᵐᵒᵖ M]
variable {N : Type y} [AddCommGroup N] [Module R N] [Module A N]
variable [IsScalarTower R A N]
variable [Module Bᵐᵒᵖ N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]

variable {M' : Type t} [AddCommGroup M'] [Module R M'] [Module Aᵐᵒᵖ M']
variable [IsScalarTower R Aᵐᵒᵖ M']

/-- The ground-ring tensor map induced by a right `A`-linear map in the first factor. -/
def mapLeftRaw (f : M →ₗ[Aᵐᵒᵖ] M') :
    Raw (R := R) (M := M) (N := N) →ₗ[R] Raw (R := R) (M := M') (N := N) :=
  TensorProduct.map (f.restrictScalars R) (LinearMap.id : N →ₗ[R] N)

/-- A right `A`-linear map in the first factor preserves the balancing relations. -/
theorem mapLeft_relations (f : M →ₗ[Aᵐᵒᵖ] M') :
    relations (R := R) (A := A) (M := M) (N := N) ≤
      Submodule.comap (mapLeftRaw (R := R) (A := A) (M := M) (N := N) f)
        (relations (R := R) (A := A) (M := M') (N := N)) := sorry

/-- The `R`-linear map on relative tensor quotients induced in the first factor. -/
def mapLeftLinear (f : M →ₗ[Aᵐᵒᵖ] M') :
    Product (R := R) (A := A) (M := M) (N := N) →ₗ[R]
      Product (R := R) (A := A) (M := M') (N := N) :=
  (relations (R := R) (A := A) (M := M) (N := N)).mapQ
    (relations (R := R) (A := A) (M := M') (N := N))
    (mapLeftRaw (R := R) (A := A) (M := M) (N := N) f) (mapLeft_relations f)

/-- Functoriality of the relative tensor product in its first, right-module factor. -/
def mapLeft (f : M →ₗ[Aᵐᵒᵖ] M') :
    Product (R := R) (A := A) (M := M) (N := N) →ₗ[Bᵐᵒᵖ]
      Product (R := R) (A := A) (M := M') (N := N) where
  toFun := mapLeftLinear (R := R) (A := A) (M := M) (N := N) f
  map_add' := sorry
  map_smul' := sorry

/-- Mapping the first factor evaluates on pure tensors as expected. -/
@[simp]
theorem mapLeft_tmul (f : M →ₗ[Aᵐᵒᵖ] M') (m : M) (n : N) :
    mapLeft (R := R) (A := A) (B := B) (N := N) f (tmul (R := R) (A := A) m n) =
      tmul (R := R) (A := A) (f m) n := sorry

/-- Mapping the identity in the first factor is the identity map. -/
@[simp]
theorem mapLeft_id :
    mapLeft (R := R) (A := A) (B := B) (N := N)
      (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) = LinearMap.id := sorry

/-- Successive maps in the first factor compose on relative tensor products. -/
theorem mapLeft_comp {M'' : Type z} [AddCommGroup M''] [Module R M''] [Module Aᵐᵒᵖ M'']
    [IsScalarTower R Aᵐᵒᵖ M''] (f : M →ₗ[Aᵐᵒᵖ] M') (g : M' →ₗ[Aᵐᵒᵖ] M'') :
    mapLeft (R := R) (A := A) (B := B) (N := N) (g.comp f) =
      (mapLeft (R := R) (A := A) (B := B) (N := N) g).comp
        (mapLeft (R := R) (A := A) (B := B) (N := N) f) := sorry

variable {N' : Type z} [AddCommGroup N'] [Module R N'] [Module A N'] [Module Bᵐᵒᵖ N']
variable [IsScalarTower R A N'] [IsScalarTower R Bᵐᵒᵖ N'] [SMulCommClass A Bᵐᵒᵖ N']

/-- The ground-ring tensor map induced by a bimodule morphism in the second factor. -/
def mapRightRaw (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Raw (R := R) (M := M) (N := N) →ₗ[R] Raw (R := R) (M := M) (N := N') :=
  TensorProduct.map (LinearMap.id : M →ₗ[R] M) ((Hom.toRightLinearMap f).restrictScalars R)

/-- A bimodule morphism in the second factor preserves the balancing relations. -/
theorem mapRight_relations
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    relations (R := R) (A := A) (M := M) (N := N) ≤
      Submodule.comap (mapRightRaw (R := R) (A := A) (M := M) f)
        (relations (R := R) (A := A) (M := M) (N := N')) := sorry

/-- The `R`-linear map on relative tensor quotients induced in the second factor. -/
def mapRightLinear (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Product (R := R) (A := A) (M := M) (N := N) →ₗ[R]
      Product (R := R) (A := A) (M := M) (N := N') :=
  (relations (R := R) (A := A) (M := M) (N := N)).mapQ
    (relations (R := R) (A := A) (M := M) (N := N'))
    (mapRightRaw (R := R) (A := A) (M := M) f) (mapRight_relations f)

/-- Functoriality of the relative tensor product in its bimodule factor. -/
def mapRight (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Product (R := R) (A := A) (M := M) (N := N) →ₗ[Bᵐᵒᵖ]
      Product (R := R) (A := A) (M := M) (N := N') where
  toFun := mapRightLinear (R := R) (A := A) (M := M) f
  map_add' := sorry
  map_smul' := sorry

/-- Mapping the second factor evaluates on pure tensors as expected. -/
@[simp]
theorem mapRight_tmul
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (m : M) (n : N) :
    mapRight (R := R) (A := A) (B := B) (M := M) f
        (tmul (R := R) (A := A) m n) =
      tmul (R := R) (A := A) m (f n) := sorry

/-- Mapping the identity in the second factor is the identity map. -/
@[simp]
theorem mapRight_id :
    mapRight (R := R) (A := A) (B := B) (M := M)
      (Hom.id (R := R) (A := A) (B := B) (N := N)) = LinearMap.id := sorry

/-- Successive bimodule maps in the second factor compose on relative tensor products. -/
theorem mapRight_comp
    {N'' : Type i} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (f : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g : Hom (R := R) (A := A) (B := B) (N := N') (N' := N'')) :
    mapRight (R := R) (A := A) (B := B) (M := M) (Hom.comp g f) =
      (mapRight (R := R) (A := A) (B := B) (M := M) g).comp
        (mapRight (R := R) (A := A) (B := B) (M := M) f) := sorry

/-- Functoriality of the concrete relative tensor product in both module variables. -/
@[stacks 09LN "functoriality of concrete relative tensor products"]
def map (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    Product (R := R) (A := A) (M := M) (N := N) →ₗ[Bᵐᵒᵖ]
      Product (R := R) (A := A) (M := M') (N := N') :=
  (mapRight (R := R) (A := A) (B := B) (M := M') g).comp
    (mapLeft (R := R) (A := A) (B := B) (N := N) f)

/-- Mapping both factors evaluates componentwise on pure tensors. -/
@[simp]
theorem map_tmul (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) (m : M) (n : N) :
    map (R := R) (A := A) (B := B) f g (tmul (R := R) (A := A) m n) =
      tmul (R := R) (A := A) (f m) (g n) := sorry

/-- Maps in the two relative tensor factors commute. -/
theorem mapLeft_mapRight (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    (mapRight (R := R) (A := A) (B := B) (M := M') g).comp
        (mapLeft (R := R) (A := A) (B := B) (N := N) f) =
      (mapLeft (R := R) (A := A) (B := B) (N := N') f).comp
        (mapRight (R := R) (A := A) (B := B) (M := M) g) := sorry

/-- The simultaneous tensor map can equivalently be formed in the opposite factor order. -/
theorem map_eq_mapLeft_comp_mapRight (f : M →ₗ[Aᵐᵒᵖ] M')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    map (R := R) (A := A) (B := B) f g =
      (mapLeft (R := R) (A := A) (B := B) (N := N') f).comp
        (mapRight (R := R) (A := A) (B := B) (M := M) g) := sorry

/-- Mapping both factors by identities is the identity relative tensor map. -/
@[simp]
theorem map_id :
    map (R := R) (A := A) (B := B)
      (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M)
      (Hom.id (R := R) (A := A) (B := B) (N := N)) = LinearMap.id := sorry

/-- The simultaneous tensor map with identity in the first factor is `mapRight`. -/
@[simp]
theorem map_id_left
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N')) :
    map (R := R) (A := A) (B := B) (LinearMap.id : M →ₗ[Aᵐᵒᵖ] M) g =
      mapRight (R := R) (A := A) (B := B) (M := M) g := sorry

/-- The simultaneous tensor map with identity in the second factor is `mapLeft`. -/
@[simp]
theorem map_id_right (f : M →ₗ[Aᵐᵒᵖ] M') :
    map (R := R) (A := A) (B := B) f
        (Hom.id (R := R) (A := A) (B := B) (N := N)) =
      mapLeft (R := R) (A := A) (B := B) (N := N) f := sorry

/-- Simultaneous relative tensor maps preserve composition in both variables. -/
theorem map_comp
    {M'' : Type i} [AddCommGroup M''] [Module R M''] [Module Aᵐᵒᵖ M'']
    [IsScalarTower R Aᵐᵒᵖ M'']
    {N'' : Type j} [AddCommGroup N''] [Module R N''] [Module A N''] [Module Bᵐᵒᵖ N'']
    [IsScalarTower R A N''] [IsScalarTower R Bᵐᵒᵖ N''] [SMulCommClass A Bᵐᵒᵖ N'']
    (f : M →ₗ[Aᵐᵒᵖ] M') (f' : M' →ₗ[Aᵐᵒᵖ] M'')
    (g : Hom (R := R) (A := A) (B := B) (N := N) (N' := N'))
    (g' : Hom (R := R) (A := A) (B := B) (N := N') (N' := N'')) :
    map (R := R) (A := A) (B := B) (f'.comp f) (Hom.comp g' g) =
      (map (R := R) (A := A) (B := B) f' g').comp
        (map (R := R) (A := A) (B := B) f g) := sorry

end RelativeTensor

end Module.Bimodule
