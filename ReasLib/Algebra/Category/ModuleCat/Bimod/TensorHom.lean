module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Module.Bimodule.TensorHom
import Mathlib.Tactic.CrossRefAttribute

/-!
# The ordinary relative tensor-Hom adjunction in module categories

This leaf organizes the universe-polymorphic concrete tensor-Hom equivalence as an adjunction
between ordinary module categories.  It does not use the monoidal structure on `ModuleCat`, so
the base ring, the two algebras, and the module carriers may live in independent universes.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra RelativeTensor

noncomputable section

universe u v w x

namespace Module.Bimodule

variable {R : Type u} {A : Type v} {B : Type w} {N : Type x}
variable [CommRing R] [Ring A] [Algebra R A] [Ring B] [Algebra R B]
variable [AddCommGroup N] [Module R N] [Module A N] [Module Bᵐᵒᵖ N]
variable [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
variable [SMulCommClass A Bᵐᵒᵖ N]

namespace RelativeTensor

namespace Functor

/-- The ground-ring module obtained from an ordinary right `A`-module by universe-polymorphic
restriction of scalars along `R → Aᵐᵒᵖ`. -/
@[stacks 09LN "restricted carrier for ordinary relative tensor products"]
abbrev restricted (M : ModuleCat.{x} Aᵐᵒᵖ) : ModuleCat.{x} R :=
  (ModuleCat.restrictScalars (algebraMap R Aᵐᵒᵖ)).obj M

end Functor

/-- Tensoring an ordinary right `A`-module with the fixed `(A, B)`-bimodule `N` defines a
functor to ordinary right `B`-modules. -/
@[stacks 09LN "ordinary relative tensor product functor"]
noncomputable def functor (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] :
    ModuleCat.{x} Aᵐᵒᵖ ⥤ ModuleCat.{x} Bᵐᵒᵖ where
  obj M := ModuleCat.of Bᵐᵒᵖ
    (Product (R := R) (A := A) (M := Functor.restricted (R := R) M) (N := N))
  map {M M'} f := ModuleCat.ofHom
    (mapLeft (R := R) (A := A) (B := B)
      (M := Functor.restricted (R := R) M)
      (M' := Functor.restricted (R := R) M') (N := N) f.hom)
  map_id := sorry
  map_comp := sorry

/-- The relative tensor functor is the concrete relative tensor quotient on objects. -/
@[simp, stacks 09LN "ordinary relative tensor product functor on objects"]
theorem functor_obj (M : ModuleCat.{x} Aᵐᵒᵖ) :
    (functor (R := R) (A := A) (B := B) N).obj M =
      ModuleCat.of Bᵐᵒᵖ
        (Product (R := R) (A := A)
          (M := Functor.restricted (R := R) M) (N := N)) := sorry

/-- The relative tensor functor maps an ordinary right-linear map by functoriality in the first
factor of the concrete relative tensor product. -/
@[simp, stacks 09LN "ordinary relative tensor product functor on morphisms"]
theorem functor_map {M M' : ModuleCat.{x} Aᵐᵒᵖ} (f : M ⟶ M') :
    (functor (R := R) (A := A) (B := B) N).map f =
      ModuleCat.ofHom
        (mapLeft (R := R) (A := A) (B := B)
          (M := Functor.restricted (R := R) M)
          (M' := Functor.restricted (R := R) M') (N := N) f.hom) := sorry

namespace Functor

/-- A pure tensor as an element of the ordinary relative tensor functor, without exposing its
quotient presentation. -/
@[stacks 09LN "pure tensors in the ordinary relative tensor functor"]
def tmul {M : ModuleCat.{x} Aᵐᵒᵖ} (m : M) (n : N) :
    (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M :=
  RelativeTensor.tmul (R := R) (A := A)
    (M := restricted (R := R) M) m n

/-- The right `B`-action on a functor-level pure tensor acts in its second factor. -/
@[simp, stacks 09LN "right action on functor-level ordinary pure tensors"]
theorem tmul_smul {M : ModuleCat.{x} Aᵐᵒᵖ} (m : M) (n : N) (b : Bᵐᵒᵖ) :
    b • tmul (R := R) (A := A) (B := B) m n =
      tmul (R := R) (A := A) (B := B) m (b • n) := sorry

/-- Prove a predicate on an object of the ordinary relative tensor functor by checking zero,
addition, and pure tensors. -/
@[elab_as_elim, induction_eliminator,
  stacks 09LN "induction on the ordinary relative tensor functor"]
protected theorem induction_on {M : ModuleCat.{x} Aᵐᵒᵖ}
    {p : ((RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M : Type x) → Prop}
    (z : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M)
    (zero : p 0)
    (tmul : ∀ m n, p (Functor.tmul (R := R) (A := A) (B := B) m n))
    (add : ∀ x y, p x → p y → p (x + y)) :
    p z := sorry

/-- Morphisms from an object of the ordinary relative tensor functor are determined on pure
tensors. -/
@[ext, stacks 09LN "extensionality for the ordinary relative tensor functor"]
theorem hom_ext {M : ModuleCat.{x} Aᵐᵒᵖ} {P : ModuleCat.{x} Bᵐᵒᵖ}
    {f g : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P}
    (h : ∀ m n,
      f.hom (tmul (R := R) (A := A) (B := B) m n) =
        g.hom (tmul (R := R) (A := A) (B := B) m n)) :
    f = g := sorry

/-- The ordinary relative tensor functor maps pure tensors in its first factor. -/
@[simp, stacks 09LN "ordinary relative tensor functor maps pure tensors"]
theorem map_tmul {M M' : ModuleCat.{x} Aᵐᵒᵖ} (f : M ⟶ M') (m : M) (n : N) :
    ((RelativeTensor.functor (R := R) (A := A) (B := B) N).map f).hom
        (tmul (R := R) (A := A) (B := B) m n) =
      tmul (R := R) (A := A) (B := B) (f.hom m) n := sorry

end Functor

end RelativeTensor

namespace InternalHom

namespace Functor

/-- The ground-ring module obtained from an ordinary right `B`-module by universe-polymorphic
restriction of scalars along `R → Bᵐᵒᵖ`. -/
@[stacks 09LN "restricted carrier for ordinary relative internal Hom"]
abbrev restricted (P : ModuleCat.{x} Bᵐᵒᵖ) : ModuleCat.{x} R :=
  (ModuleCat.restrictScalars (algebraMap R Bᵐᵒᵖ)).obj P

end Functor

/-- Taking the concrete right-`B`-linear internal Hom out of the fixed bimodule `N` defines a
functor from ordinary right `B`-modules to ordinary right `A`-modules. -/
@[stacks 09LN "ordinary relative internal Hom functor"]
noncomputable def functor (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] :
    ModuleCat.{x} Bᵐᵒᵖ ⥤ ModuleCat.{x} Aᵐᵒᵖ where
  obj P := ModuleCat.of Aᵐᵒᵖ
    (InternalHom B N (Functor.restricted (R := R) P))
  map {P Q} f := ModuleCat.ofHom
    (mapTarget (A := A) (B := B) (N := N)
      (P := Functor.restricted (R := R) P)
      (Q := Functor.restricted (R := R) Q) f.hom)
  map_id := sorry
  map_comp := sorry

namespace Functor

/-- The carrier of an object of the ordinary internal-Hom functor is linearly equivalent to the
wrapped right-linear-map space used by the concrete API. -/
@[stacks 09LN "carrier of the ordinary relative internal Hom functor"]
noncomputable def objLinearEquiv (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] (P : ModuleCat.{x} Bᵐᵒᵖ) :
    ((InternalHom.functor (R := R) (A := A) (B := B) N).obj P : Type x) ≃ₗ[Aᵐᵒᵖ]
      InternalHom B N (restricted (R := R) P) :=
  LinearEquiv.refl Aᵐᵒᵖ _

/-- An element of an ordinary internal-Hom functor object as its underlying right-linear map. -/
@[stacks 09LN "underlying map of an ordinary relative internal Hom element"]
def toLinearMap (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) :
    N →ₗ[Bᵐᵒᵖ] P :=
  (objLinearEquiv (R := R) (A := A) (B := B) N P f).toLinearMap

/-- Evaluation of an element of an ordinary internal-Hom functor object. -/
@[stacks 09LN "evaluation in the ordinary relative internal Hom functor"]
def eval (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) (n : N) : P :=
  toLinearMap (R := R) (A := A) (B := B) (N := N) P f n

/-- Evaluation in the ordinary internal-Hom functor agrees with the wrapped concrete map. -/
@[simp, stacks 09LN "ordinary relative internal Hom evaluation formula"]
theorem eval_eq (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) (n : N) :
    eval (R := R) (A := A) (B := B) P f n =
      objLinearEquiv (R := R) (A := A) (B := B) N P f n := sorry

/-- Elements of an ordinary internal-Hom functor object are determined by evaluation. -/
@[ext, stacks 09LN "extensionality for the ordinary relative internal Hom functor"]
theorem hom_ext (P : ModuleCat.{x} Bᵐᵒᵖ)
    {f g : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P}
    (h : ∀ n, eval (R := R) (A := A) (B := B) P f n =
      eval (R := R) (A := A) (B := B) P g n) :
    f = g := sorry

end Functor

/-- The internal-Hom functor is the concrete relative internal Hom on objects. -/
@[simp, stacks 09LN "ordinary relative internal Hom functor on objects"]
theorem functor_obj (P : ModuleCat.{x} Bᵐᵒᵖ) :
    (functor (R := R) (A := A) (B := B) N).obj P =
      ModuleCat.of Aᵐᵒᵖ
        (InternalHom B N (Functor.restricted (R := R) P)) := sorry

/-- The internal-Hom functor maps an ordinary right-`B`-linear map by postcomposition. -/
@[simp, stacks 09LN "ordinary relative internal Hom functor on morphisms"]
theorem functor_map {P Q : ModuleCat.{x} Bᵐᵒᵖ} (f : P ⟶ Q) :
    (functor (R := R) (A := A) (B := B) N).map f =
      ModuleCat.ofHom
        (mapTarget (A := A) (B := B) (N := N)
          (P := Functor.restricted (R := R) P)
          (Q := Functor.restricted (R := R) Q) f.hom) := sorry

namespace Functor

/-- The ordinary internal-Hom functor acts on evaluation by postcomposition. -/
@[simp, stacks 09LN "ordinary relative internal Hom functor on evaluation"]
theorem map_eval {P Q : ModuleCat.{x} Bᵐᵒᵖ} (f : P ⟶ Q)
    (g : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) (n : N) :
    eval (R := R) (A := A) (B := B) Q
        (((InternalHom.functor (R := R) (A := A) (B := B) N).map f).hom g) n =
      f.hom (eval (R := R) (A := A) (B := B) P g n) := sorry

end Functor

end InternalHom

namespace TensorHom

/-- The categorical hom-set equivalence obtained by bundling the concrete tensor-Hom
equivalence as morphisms of ordinary module categories. -/
@[stacks 09LN "ordinary module-category tensor-Hom equivalence"]
noncomputable def homEquiv (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N]
    (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ) :
    ((RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P) ≃
      (M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) where
  toFun f := ModuleCat.ofHom
    (equiv (R := R) (A := A) (B := B)
      (M := RelativeTensor.Functor.restricted (R := R) M) (N := N)
      (P := InternalHom.Functor.restricted (R := R) P) f.hom)
  invFun g := ModuleCat.ofHom
    ((equiv (R := R) (A := A) (B := B)
      (M := RelativeTensor.Functor.restricted (R := R) M) (N := N)
      (P := InternalHom.Functor.restricted (R := R) P)).symm g.hom)
  left_inv := sorry
  right_inv := sorry

/-- On underlying linear maps, categorical tensor-Hom currying is the concrete equivalence. -/
@[simp, stacks 09LN "ordinary module-category tensor-Hom equivalence forward map"]
theorem homEquiv_apply (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P) :
    (homEquiv (R := R) (A := A) (B := B) N M P f).hom =
      equiv (R := R) (A := A) (B := B)
        (M := RelativeTensor.Functor.restricted (R := R) M) (N := N)
        (P := InternalHom.Functor.restricted (R := R) P) f.hom := sorry

/-- Categorical tensor-Hom currying evaluates a map on a pair by evaluating it on the
corresponding pure relative tensor. -/
@[simp, stacks 09LN "ordinary module-category tensor-Hom evaluation"]
theorem homEquiv_apply_apply (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P)
    (m : M) (n : N) :
    InternalHom.Functor.eval (R := R) (A := A) (B := B) P
        (homEquiv (R := R) (A := A) (B := B) N M P f m) n =
      f.hom (RelativeTensor.Functor.tmul (R := R) (A := A) (B := B) m n) := sorry

/-- On underlying linear maps, inverse categorical tensor-Hom currying is concrete
uncurrying. -/
@[simp, stacks 09LN "ordinary module-category tensor-Hom equivalence inverse map"]
theorem homEquiv_symm_apply (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ)
    (g : M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) :
    ((homEquiv (R := R) (A := A) (B := B) N M P).symm g).hom =
      (equiv (R := R) (A := A) (B := B)
        (M := RelativeTensor.Functor.restricted (R := R) M) (N := N)
        (P := InternalHom.Functor.restricted (R := R) P)).symm g.hom := sorry

/-- Inverse categorical tensor-Hom currying evaluates on a pure tensor by applying the curried
map to both factors. -/
@[simp, stacks 09LN "inverse ordinary module-category tensor-Hom evaluation"]
theorem homEquiv_symm_apply_tmul (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ)
    (g : M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P)
    (m : M) (n : N) :
    ((homEquiv (R := R) (A := A) (B := B) N M P).symm g).hom
        (RelativeTensor.Functor.tmul (R := R) (A := A) (B := B) m n) =
      InternalHom.Functor.eval (R := R) (A := A) (B := B) P (g.hom m) n := sorry

variable {M M' : ModuleCat.{x} Aᵐᵒᵖ} {P Q : ModuleCat.{x} Bᵐᵒᵖ}

/-- The categorical tensor-Hom equivalence is contravariantly natural in the right
`A`-module. -/
@[stacks 09LN "naturality of ordinary module-category tensor-Hom currying"]
theorem homEquiv_naturality_left (f : M' ⟶ M)
    (g : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P) :
    homEquiv (R := R) (A := A) (B := B) N M' P
        ((RelativeTensor.functor (R := R) (A := A) (B := B) N).map f ≫ g) =
      f ≫ homEquiv (R := R) (A := A) (B := B) N M P g := sorry

/-- Inverse categorical tensor-Hom currying is contravariantly natural in the right
`A`-module. -/
@[stacks 09LN "inverse naturality of ordinary module-category tensor-Hom currying"]
theorem homEquiv_naturality_left_symm (f : M' ⟶ M)
    (g : M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) :
    (homEquiv (R := R) (A := A) (B := B) N M' P).symm (f ≫ g) =
      (RelativeTensor.functor (R := R) (A := A) (B := B) N).map f ≫
        (homEquiv (R := R) (A := A) (B := B) N M P).symm g := sorry

/-- The categorical tensor-Hom equivalence is covariantly natural in the target right
`B`-module. -/
@[stacks 09LN "target naturality of ordinary module-category tensor-Hom currying"]
theorem homEquiv_naturality_right
    (f : (RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M ⟶ P)
    (g : P ⟶ Q) :
    homEquiv (R := R) (A := A) (B := B) N M Q (f ≫ g) =
      homEquiv (R := R) (A := A) (B := B) N M P f ≫
        (InternalHom.functor (R := R) (A := A) (B := B) N).map g := sorry

/-- Inverse categorical tensor-Hom currying is covariantly natural in the target right
`B`-module. -/
@[stacks 09LN "inverse target naturality of ordinary module-category tensor-Hom currying"]
theorem homEquiv_naturality_right_symm
    (f : M ⟶ (InternalHom.functor (R := R) (A := A) (B := B) N).obj P)
    (g : P ⟶ Q) :
    (homEquiv (R := R) (A := A) (B := B) N M Q).symm
        (f ≫ (InternalHom.functor (R := R) (A := A) (B := B) N).map g) =
      (homEquiv (R := R) (A := A) (B := B) N M P).symm f ≫ g := sorry

/-- The natural hom-set equivalences forming the ordinary relative tensor-Hom adjunction. -/
@[stacks 09LN "ordinary relative tensor-Hom adjunction core"]
noncomputable def coreHomEquiv (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] :
    Adjunction.CoreHomEquiv
      (RelativeTensor.functor (R := R) (A := A) (B := B) N)
      (InternalHom.functor (R := R) (A := A) (B := B) N) where
  homEquiv := homEquiv (R := R) (A := A) (B := B) N
  homEquiv_naturality_left_symm := homEquiv_naturality_left_symm (R := R) (N := N)
  homEquiv_naturality_right := homEquiv_naturality_right (R := R) (N := N)

/-- The ordinary relative tensor functor with `N` is left adjoint to relative internal Hom out
of `N`. -/
@[stacks 09LN "ordinary relative tensor-Hom adjunction"]
noncomputable def adjunction (N : Type x) [AddCommGroup N] [Module R N] [Module A N]
    [Module Bᵐᵒᵖ N] [IsScalarTower R A N] [IsScalarTower R Bᵐᵒᵖ N]
    [SMulCommClass A Bᵐᵒᵖ N] :
    RelativeTensor.functor (R := R) (A := A) (B := B) N ⊣
      InternalHom.functor (R := R) (A := A) (B := B) N :=
  Adjunction.mkOfHomEquiv (coreHomEquiv (R := R) (A := A) (B := B) N)

/-- The hom-set equivalence of `adjunction N` is the bundled concrete tensor-Hom
equivalence. -/
@[simp, stacks 09LN "ordinary relative tensor-Hom adjunction equivalence"]
theorem adjunction_homEquiv (M : ModuleCat.{x} Aᵐᵒᵖ) (P : ModuleCat.{x} Bᵐᵒᵖ) :
    (adjunction (R := R) (A := A) (B := B) N).homEquiv M P =
      homEquiv (R := R) (A := A) (B := B) N M P := sorry

/-- The unit of the ordinary tensor-Hom adjunction is currying of the identity map. -/
@[stacks 09LN "ordinary relative tensor-Hom adjunction unit"]
theorem adjunction_unit_app (M : ModuleCat.{x} Aᵐᵒᵖ) :
    (adjunction (R := R) (A := A) (B := B) N).unit.app M =
      homEquiv (R := R) (A := A) (B := B) N M
        ((RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M) (𝟙 _) := sorry

/-- The unit sends `m` to the map `n ↦ m ⊗ᵣ n`. -/
@[simp, stacks 09LN "ordinary relative tensor-Hom adjunction unit evaluation"]
theorem adjunction_unit_app_apply (M : ModuleCat.{x} Aᵐᵒᵖ) (m : M) (n : N) :
    InternalHom.Functor.eval (R := R) (A := A) (B := B)
        ((RelativeTensor.functor (R := R) (A := A) (B := B) N).obj M)
        ((adjunction (R := R) (A := A) (B := B) N).unit.app M m) n =
      RelativeTensor.Functor.tmul (R := R) (A := A) (B := B) m n := sorry

/-- The counit of the ordinary tensor-Hom adjunction is uncurrying of the identity map. -/
@[stacks 09LN "ordinary relative tensor-Hom adjunction counit"]
theorem adjunction_counit_app (P : ModuleCat.{x} Bᵐᵒᵖ) :
    (adjunction (R := R) (A := A) (B := B) N).counit.app P =
      (homEquiv (R := R) (A := A) (B := B) N
        ((InternalHom.functor (R := R) (A := A) (B := B) N).obj P) P).symm (𝟙 _) := sorry

/-- The counit evaluates a pure tensor `f ⊗ᵣ n` as `f n`. -/
@[simp, stacks 09LN "ordinary relative tensor-Hom adjunction counit evaluation"]
theorem adjunction_counit_app_tmul (P : ModuleCat.{x} Bᵐᵒᵖ)
    (f : (InternalHom.functor (R := R) (A := A) (B := B) N).obj P) (n : N) :
    (adjunction (R := R) (A := A) (B := B) N).counit.app P
        (RelativeTensor.Functor.tmul (R := R) (A := A) (B := B) f n) =
      InternalHom.Functor.eval (R := R) (A := A) (B := B) P f n := sorry

end TensorHom

namespace RelativeTensor

/-- Tensoring with a fixed ordinary bimodule is additive on module-category morphisms. -/
@[stacks 09LN "ordinary relative tensor product functor is additive"]
instance functorAdditive :
    (functor (R := R) (A := A) (B := B) N).Additive := sorry

/-- Tensoring with a fixed ordinary bimodule is `R`-linear on module-category morphisms. -/
@[stacks 09LN "ordinary relative tensor product functor is linear"]
instance functorLinear :
    CategoryTheory.Functor.Linear R
      (functor (R := R) (A := A) (B := B) N) := sorry

/-- The ordinary relative tensor functor is canonically recognized as a left adjoint. -/
@[stacks 09LN "ordinary relative tensor product is a left adjoint"]
instance functorIsLeftAdjoint :
    (functor (R := R) (A := A) (B := B) N).IsLeftAdjoint := sorry

end RelativeTensor

namespace InternalHom

/-- Relative internal Hom out of a fixed ordinary bimodule is additive on module-category
morphisms. -/
@[stacks 09LN "ordinary relative internal Hom functor is additive"]
instance functorAdditive :
    (functor (R := R) (A := A) (B := B) N).Additive := sorry

/-- Relative internal Hom out of a fixed ordinary bimodule is `R`-linear on module-category
morphisms. -/
@[stacks 09LN "ordinary relative internal Hom functor is linear"]
instance functorLinear :
    CategoryTheory.Functor.Linear R
      (functor (R := R) (A := A) (B := B) N) := sorry

/-- The ordinary relative internal-Hom functor is canonically recognized as a right adjoint. -/
@[stacks 09LN "ordinary relative internal Hom is a right adjoint"]
instance functorIsRightAdjoint :
    (functor (R := R) (A := A) (B := B) N).IsRightAdjoint := sorry

end InternalHom

#synth (RelativeTensor.functor (R := R) (A := A) (B := B) N).IsLeftAdjoint
#synth (InternalHom.functor (R := R) (A := A) (B := B) N).IsRightAdjoint
#synth (RelativeTensor.functor (R := R) (A := A) (B := B) N).Additive
#synth CategoryTheory.Functor.Linear R
  (RelativeTensor.functor (R := R) (A := A) (B := B) N)
#synth (InternalHom.functor (R := R) (A := A) (B := B) N).Additive
#synth CategoryTheory.Functor.Linear R
  (InternalHom.functor (R := R) (A := A) (B := B) N)

end Module.Bimodule
