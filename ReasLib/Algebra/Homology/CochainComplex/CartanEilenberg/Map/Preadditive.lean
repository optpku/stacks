/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Category

/-!
# Additive maps of Cartan--Eilenberg resolutions

This leaf equips maps between fixed Cartan--Eilenberg resolutions with the canonical additive
operations and equips bundled resolutions with their preadditive category structure.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}
variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

namespace Map

/-- The augmentation law for the zero map of two fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "augmentation compatibility of the zero map"]
theorem zero_augmentation_naturality :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (0 : I.bicomplex ⟶ J.bicomplex)).f 0 =
      (0 : K ⟶ L).hom ≫ J.augmentation := sorry

/-- The zero map of two fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "zero map of Cartan-Eilenberg resolutions"]
def zero : Map I J where
  base := 0
  hom := 0
  augmentation_naturality := zero_augmentation_naturality

/-- The augmentation law for the sum of two maps of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "augmentation compatibility of sums of maps"]
theorem add_augmentation_naturality (f g : Map I J) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (f.hom + g.hom)).f 0 =
      (f.base + g.base).hom ≫ J.augmentation := sorry

/-- The sum of two maps of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "addition of Cartan-Eilenberg resolution maps"]
def add (f g : Map I J) : Map I J where
  base := f.base + g.base
  hom := f.hom + g.hom
  augmentation_naturality := add_augmentation_naturality f g

/-- The augmentation law for the additive inverse of a map of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "augmentation compatibility of negated maps"]
theorem neg_augmentation_naturality (f : Map I J) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (-f.hom)).f 0 =
      (-f.base).hom ≫ J.augmentation := sorry

/-- The additive inverse of a map of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "negation of Cartan-Eilenberg resolution maps"]
def neg (f : Map I J) : Map I J where
  base := -f.base
  hom := -f.hom
  augmentation_naturality := neg_augmentation_naturality f

/-- The augmentation law for the difference of two maps of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "augmentation compatibility of differences of maps"]
theorem sub_augmentation_naturality (f g : Map I J) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (f.hom - g.hom)).f 0 =
      (f.base - g.base).hom ≫ J.augmentation := sorry

/-- The difference of two maps of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "subtraction of Cartan-Eilenberg resolution maps"]
def sub (f g : Map I J) : Map I J where
  base := f.base - g.base
  hom := f.hom - g.hom
  augmentation_naturality := sub_augmentation_naturality f g

/-- The augmentation law for natural-number multiples of resolution maps. -/
@[stacks 015J "augmentation compatibility of natural-number multiples"]
theorem nsmul_augmentation_naturality (n : ℕ) (f : Map I J) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (n • f.hom)).f 0 =
      (n • f.base).hom ≫ J.augmentation := sorry

/-- The natural-number multiple of a map of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "natural-number multiples of Cartan-Eilenberg resolution maps"]
def nsmul (n : ℕ) (f : Map I J) : Map I J where
  base := n • f.base
  hom := n • f.hom
  augmentation_naturality := nsmul_augmentation_naturality n f

/-- The augmentation law for integer multiples of resolution maps. -/
@[stacks 015J "augmentation compatibility of integer multiples"]
theorem zsmul_augmentation_naturality (n : ℤ) (f : Map I J) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (n • f.hom)).f 0 =
      (n • f.base).hom ≫ J.augmentation := sorry

/-- The integer multiple of a map of fixed Cartan--Eilenberg resolutions. -/
@[stacks 015J "integer multiples of Cartan-Eilenberg resolution maps"]
def zsmul (n : ℤ) (f : Map I J) : Map I J where
  base := n • f.base
  hom := n • f.hom
  augmentation_naturality := zsmul_augmentation_naturality n f

/-- The additive zero operation on Cartan--Eilenberg resolution maps. -/
instance : Zero (Map I J) := ⟨zero⟩

/-- The additive sum operation on Cartan--Eilenberg resolution maps. -/
instance : Add (Map I J) := ⟨add⟩

/-- The additive inverse operation on Cartan--Eilenberg resolution maps. -/
instance : Neg (Map I J) := ⟨neg⟩

/-- The additive difference operation on Cartan--Eilenberg resolution maps. -/
instance : Sub (Map I J) := ⟨sub⟩

/-- Natural-number scalar multiplication on Cartan--Eilenberg resolution maps. -/
instance : SMul ℕ (Map I J) := ⟨nsmul⟩

/-- Integer scalar multiplication on Cartan--Eilenberg resolution maps. -/
instance : SMul ℤ (Map I J) := ⟨zsmul⟩

/-- The base component of the zero map. -/
@[simp] theorem zero_base : (zero : Map I J).base = 0 := sorry

/-- The double-complex component of the zero map. -/
@[simp] theorem zero_hom : (zero : Map I J).hom = 0 := sorry

/-- The base component of a sum. -/
@[simp] theorem add_base (f g : Map I J) : (f + g).base = f.base + g.base := sorry

/-- The double-complex component of a sum. -/
@[simp] theorem add_hom (f g : Map I J) : (f + g).hom = f.hom + g.hom := sorry

/-- The base component of an additive inverse. -/
@[simp] theorem neg_base (f : Map I J) : (-f).base = -f.base := sorry

/-- The double-complex component of an additive inverse. -/
@[simp] theorem neg_hom (f : Map I J) : (-f).hom = -f.hom := sorry

/-- The base component of a difference. -/
@[simp] theorem sub_base (f g : Map I J) : (f - g).base = f.base - g.base := sorry

/-- The double-complex component of a difference. -/
@[simp] theorem sub_hom (f g : Map I J) : (f - g).hom = f.hom - g.hom := sorry

/-- The base component of a natural-number multiple. -/
@[simp] theorem nsmul_base (n : ℕ) (f : Map I J) : (n • f).base = n • f.base := sorry

/-- The double-complex component of a natural-number multiple. -/
@[simp] theorem nsmul_hom (n : ℕ) (f : Map I J) : (n • f).hom = n • f.hom := sorry

/-- The base component of an integer multiple. -/
@[simp] theorem zsmul_base (n : ℤ) (f : Map I J) : (n • f).base = n • f.base := sorry

/-- The double-complex component of an integer multiple. -/
@[simp] theorem zsmul_hom (n : ℤ) (f : Map I J) : (n • f).hom = n • f.hom := sorry

/-- Maps are determined by their two additive components. -/
theorem pair_injective :
    Function.Injective (fun f : Map I J => (f.base, f.hom)) :=
  sorry

/-- The componentwise zero law for resolution maps. -/
theorem pair_zero :
    (fun f : Map I J => (f.base, f.hom)) (0 : Map I J) = 0 := sorry

/-- The componentwise addition law for resolution maps. -/
theorem pair_add (f g : Map I J) :
    (fun f : Map I J => (f.base, f.hom)) (f + g) =
      (fun f : Map I J => (f.base, f.hom)) f +
        (fun f : Map I J => (f.base, f.hom)) g := sorry

/-- The componentwise negation law for resolution maps. -/
theorem pair_neg (f : Map I J) :
    (fun f : Map I J => (f.base, f.hom)) (-f) =
      -(fun f : Map I J => (f.base, f.hom)) f := sorry

/-- The componentwise subtraction law for resolution maps. -/
theorem pair_sub (f g : Map I J) :
    (fun f : Map I J => (f.base, f.hom)) (f - g) =
      (fun f : Map I J => (f.base, f.hom)) f -
        (fun f : Map I J => (f.base, f.hom)) g := sorry

/-- The componentwise natural-number scalar law for resolution maps. -/
theorem pair_nsmul (f : Map I J) (n : ℕ) :
    (fun f : Map I J => (f.base, f.hom)) (n • f) =
      n • (fun f : Map I J => (f.base, f.hom)) f := sorry

/-- The componentwise integer scalar law for resolution maps. -/
theorem pair_zsmul (f : Map I J) (n : ℤ) :
    (fun f : Map I J => (f.base, f.hom)) (n • f) =
      n • (fun f : Map I J => (f.base, f.hom)) f := sorry

/-- Cartan--Eilenberg resolution maps form an additive commutative group. -/
@[stacks 015J "additive group of Cartan-Eilenberg resolution maps"]
instance addCommGroup : AddCommGroup (Map I J) :=
  Function.Injective.addCommGroup (fun f : Map I J => (f.base, f.hom)) pair_injective
    pair_zero pair_add pair_neg pair_sub pair_nsmul pair_zsmul

/-- Left composition preserves addition of Cartan--Eilenberg resolution maps. -/
theorem add_comp (f g : Map I J) (h : Map J N) :
    (f + g).comp h = f.comp h + g.comp h := sorry

/-- Right composition preserves addition of Cartan--Eilenberg resolution maps. -/
theorem comp_add (f : Map I J) (g h : Map J N) :
    f.comp (g + h) = f.comp g + f.comp h := sorry

/-- Left composition preserves additive inverses of Cartan--Eilenberg resolution maps. -/
theorem neg_comp (f : Map I J) (h : Map J N) :
    (neg f).comp h = neg (f.comp h) := sorry

/-- Right composition preserves additive inverses of Cartan--Eilenberg resolution maps. -/
theorem comp_neg (f : Map I J) (h : Map J N) :
    f.comp (neg h) = neg (f.comp h) := sorry

/-- Left composition preserves subtraction of Cartan--Eilenberg resolution maps. -/
theorem sub_comp (f g : Map I J) (h : Map J N) :
    (sub f g).comp h = sub (f.comp h) (g.comp h) := sorry

/-- Right composition preserves subtraction of Cartan--Eilenberg resolution maps. -/
theorem comp_sub (f : Map I J) (g h : Map J N) :
    f.comp (sub g h) = sub (f.comp g) (f.comp h) := sorry

end Map

namespace Bundled

/-- The additive commutative group on a bundled resolution hom-set. -/
@[stacks 015J "additive hom-set of bundled Cartan-Eilenberg resolutions"]
instance homAddCommGroup (X Y : Bundled A) : AddCommGroup (X ⟶ Y) := Map.addCommGroup

/-- Composition on the left distributes over addition in bundled resolutions. -/
theorem add_comp {P Q R : Bundled A} (f f' : P ⟶ Q) (g : Q ⟶ R) :
    (f + f') ≫ g = f ≫ g + f' ≫ g := sorry

/-- Composition on the right distributes over addition in bundled resolutions. -/
theorem comp_add {P Q R : Bundled A} (f : P ⟶ Q) (g g' : Q ⟶ R) :
    f ≫ (g + g') = f ≫ g + f ≫ g' := sorry

/-- Bundled Cartan--Eilenberg resolutions form a preadditive category. -/
@[stacks 015J "preadditive category of Cartan-Eilenberg resolutions"]
instance preadditive : Preadditive (Bundled A) where
  homGroup := homAddCommGroup
  add_comp := fun _ _ _ f f' g => Bundled.add_comp f f' g
  comp_add := fun _ _ _ f g g' => Bundled.comp_add f g g'

/-- The source functor on bundled resolutions is additive. -/
@[stacks 015J "additive source functor of Cartan-Eilenberg resolutions"]
instance source_additive : (source A).Additive := sorry

/-- The resolving double-complex functor on bundled resolutions is additive. -/
@[stacks 015J "additive bicomplex functor of Cartan-Eilenberg resolutions"]
instance bicomplex_additive : (bicomplex A).Additive := sorry

/-- The source functor preserves zero morphisms. -/
theorem source_map_zero {X Y : Bundled A} :
    (source A).map (0 : X ⟶ Y) = 0 := sorry

/-- The source functor preserves addition of morphisms. -/
theorem source_map_add {X Y : Bundled A} (f g : X ⟶ Y) :
    (source A).map (f + g) = (source A).map f + (source A).map g := sorry

/-- The source functor preserves additive inverses. -/
theorem source_map_neg {X Y : Bundled A} (f : X ⟶ Y) :
    (source A).map (-f) = -(source A).map f := sorry

/-- The source functor preserves subtraction. -/
theorem source_map_sub {X Y : Bundled A} (f g : X ⟶ Y) :
    (source A).map (f - g) = (source A).map f - (source A).map g := sorry

/-- The source functor preserves natural-number scalar multiplication. -/
theorem source_map_nsmul {X Y : Bundled A} (n : ℕ) (f : X ⟶ Y) :
    (source A).map (n • f) = n • (source A).map f := sorry

/-- The source functor preserves integer scalar multiplication. -/
theorem source_map_zsmul {X Y : Bundled A} (n : ℤ) (f : X ⟶ Y) :
    (source A).map (n • f) = n • (source A).map f := sorry

/-- The resolving double-complex functor preserves zero morphisms. -/
theorem bicomplex_map_zero {X Y : Bundled A} :
    (bicomplex A).map (0 : X ⟶ Y) = 0 := sorry

/-- The resolving double-complex functor preserves addition of morphisms. -/
theorem bicomplex_map_add {X Y : Bundled A} (f g : X ⟶ Y) :
    (bicomplex A).map (f + g) = (bicomplex A).map f + (bicomplex A).map g := sorry

/-- The resolving double-complex functor preserves additive inverses. -/
theorem bicomplex_map_neg {X Y : Bundled A} (f : X ⟶ Y) :
    (bicomplex A).map (-f) = -(bicomplex A).map f := sorry

/-- The resolving double-complex functor preserves subtraction. -/
theorem bicomplex_map_sub {X Y : Bundled A} (f g : X ⟶ Y) :
    (bicomplex A).map (f - g) = (bicomplex A).map f - (bicomplex A).map g := sorry

/-- The resolving double-complex functor preserves natural-number scalar multiplication. -/
theorem bicomplex_map_nsmul {X Y : Bundled A} (n : ℕ) (f : X ⟶ Y) :
    (bicomplex A).map (n • f) = n • (bicomplex A).map f := sorry

/-- The resolving double-complex functor preserves integer scalar multiplication. -/
theorem bicomplex_map_zsmul {X Y : Bundled A} (n : ℤ) (f : X ⟶ Y) :
    (bicomplex A).map (n • f) = n • (bicomplex A).map f := sorry

end Bundled

end CochainComplex.CartanEilenbergResolution
