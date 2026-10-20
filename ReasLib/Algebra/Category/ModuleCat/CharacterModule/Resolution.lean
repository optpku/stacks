module

public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Evaluation
public import ReasLib.Algebra.Category.ModuleCat.CharacterModule.Functor.MonoEpi
public import ReasLib.Algebra.Category.ModuleCat.Free.Adjunction
public import ReasLib.CategoryTheory.Abelian.FunctorialInjectives.Definition
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Functorial injective embeddings from character modules

For a left module `M` over an arbitrary ring `R`, this file implements the
source construction `J(M) = CharacterModule (F (CharacterModule M))` with
`F` taken over `Rᵐᵒᵖ`. The second character dual is transported along
`RingEquiv.opOp R`; evaluation followed by dualization of the free-module
counit gives a natural embedding `M ⟶ J(M)`.

@stack 01DC
@stack 01DD
-/

open CategoryTheory

noncomputable section

universe u v

namespace CharacterModule.Resolution

variable (R : Type u) [Ring R]

/-- The endofunctor `M ↦ CharacterModule (F (CharacterModule M))` for an
arbitrary ring.  The free module is formed over `Rᵐᵒᵖ`, where the first
character dual naturally lives. -/
@[stacks 01DD "character-module injective-target functor"]
noncomputable abbrev functor :
    ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  (CharacterModule.opFunctor R).rightOp ⋙
    (CategoryTheory.forget (ModuleCat.{max u v} Rᵐᵒᵖ) ⋙
      ModuleCat.Free.functor.{u, v} Rᵐᵒᵖ).op ⋙
      CharacterModule.opFunctor Rᵐᵒᵖ ⋙
      ModuleCat.restrictScalars (RingEquiv.opOp R).toRingHom

/-- The free module over `Rᵐᵒᵖ` on the underlying set of the character
module of `M`. -/
@[stacks 01DD "free opposite-ring module in the character resolution"]
noncomputable abbrev freeObj (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} Rᵐᵒᵖ :=
  ModuleCat.Free.obj Rᵐᵒᵖ (CharacterModule M)

/-- The canonical injective target `J(M) = CharacterModule (F
(CharacterModule M))`, with the second character dual transported from
`Rᵐᵒᵖᵐᵒᵖ` to `R`. -/
@[stacks 01DC "explicit character-module injective target"]
noncomputable abbrev obj (M : ModuleCat.{max u v} R) :
    ModuleCat.{max u v} R :=
  ModuleCat.of R (CharacterModule (freeObj R M))

/-- The objectwise form of the character-module resolution functor is the
explicit module `J(M)`. -/
@[simp]
theorem functor_obj (M : ModuleCat.{max u v} R) :
    (functor R).obj M = obj R M := sorry
/- Proof strategy: unfold `functor`, `freeObj`, and `obj`; the two sides are
definitionally equal. -/

/-- The explicit value of the embedding at an element of `M`, as a
character on the free `Rᵐᵒᵖ`-module. -/
@[stacks 01DD "pointwise character-module embedding value"]
def ιAppValue (M : ModuleCat.{max u v} R) :
    M →+ CharacterModule (freeObj R M) :=
  ((CharacterModule.dualOpposite
      ((ModuleCat.Free.counit.{u, v} Rᵐᵒᵖ).app
        ((CharacterModule.opFunctor R).obj (Opposite.op M))).hom).toAddMonoidHom).comp
    (CharacterModule.eval : M →+ CharacterModule (CharacterModule M))

/-- The underlying additive embedding into the character-module target. -/
@[stacks 01DD "additive character-module embedding"]
def ιAppAdd (M : ModuleCat.{max u v} R) :
    (forget₂ (ModuleCat R) AddCommGrpCat).obj M ⟶
      (forget₂ (ModuleCat R) AddCommGrpCat).obj (obj R M) :=
  AddCommGrpCat.ofHom (ιAppValue R M)

/-- The explicit additive embedding commutes with the `R`-actions. -/
theorem ιApp_smul_naturality (M : ModuleCat.{max u v} R) (r : R) :
    ιAppAdd R M ≫ (obj R M).smul r = M.smul r ≫ ιAppAdd R M := sorry

/-- The bundled map from `M` into its character-module injective target. -/
@[stacks 01DD "canonical map into the character-module injective target"]
noncomputable def ιApp (M : ModuleCat.{max u v} R) : M ⟶ obj R M :=
  ModuleCat.homMk (ιAppAdd R M) (ιApp_smul_naturality R M)

/-- The canonical maps `M ⟶ J(M)` are natural in `M`. -/
theorem ι_naturality {M N : ModuleCat.{max u v} R} (f : M ⟶ N) :
    f ≫ ιApp R N = ιApp R M ≫ (functor R).map f := sorry
/- Proof strategy: expand `ιApp`; use naturality of character evaluation,
naturality of the free-forget counit, and functoriality of character duality. -/

/-- The canonical embeddings assemble into a natural transformation. -/
@[stacks 01DD "functorial character-module embedding"]
noncomputable def ι : 𝟭 (ModuleCat.{max u v} R) ⟶ functor R where
  app := ιApp R
  naturality := fun {_ _} f ↦ ι_naturality R f

/-- The source construction as a functor to the arrow category. -/
@[stacks 01DD "functor of character-module injective embeddings"]
noncomputable abbrev arrowFunctor :
    ModuleCat.{max u v} R ⥤ Arrow (ModuleCat.{max u v} R) :=
  (ι R).arrowFunctor

/-- The canonical embedding is evaluation on the free `Rᵐᵒᵖ`-generators of
`F(CharacterModule M)`. -/
@[simp]
theorem ιAppValue_freeMk (M : ModuleCat.{max u v} R) (m : M)
    (χ : CharacterModule M) :
    ιAppValue R M m (ModuleCat.Free.mk Rᵐᵒᵖ χ) = χ m := sorry
/- Proof strategy: unfold `ιAppValue`, use the application formula for
`CharacterModule.dualOpposite`, and the free-forget counit formula on
`ModuleCat.Free.mk`. -/

/-- Every canonical map `M ⟶ J(M)` is injective on elements. -/
theorem ιApp_injective (M : ModuleCat.{max u v} R) :
    Function.Injective (ιApp R M) := sorry
/- Proof strategy: evaluate the target character on the free generator
`ModuleCat.Free.mk Rᵐᵒᵖ χ`. Equality of images then implies equality under
`CharacterModule.eval`, so `CharacterModule.eval_injective` concludes. The
same argument is valid after the `Rᵐᵒᵖᵐᵒᵖ`-to-`R` scalar transport. -/

/-- Every canonical map `M ⟶ J(M)` is a monomorphism. -/
@[stacks 01DC "character-module embedding is monic"]
instance mono_ιApp (M : ModuleCat.{max u v} R) : Mono (ιApp R M) := sorry
/- Proof strategy: use `mono_opEvaluationApp`, the opposite-ring dual
mono criterion, and `ModuleCat.Free.counit_app_epi`, together with
preservation of monomorphisms by restriction of scalars. -/

/-- Lemma 15.55.8, tag `01DC`: the explicit module `J(M)` is injective. -/
@[stacks 01DC "injectivity of the character-module target"]
theorem injective (M : ModuleCat.{max u v} R) :
    Module.Injective R (obj R M) := sorry
/- Proof strategy: apply the injectivity criterion for the character dual of
the free `Rᵐᵒᵖ`-module, then transport the resulting
`Rᵐᵒᵖᵐᵒᵖ`-module along `RingEquiv.opOp R`. -/

/-- The categorical form of injectivity of `J(M)`. -/
@[stacks 01DC "character-module target is injective"]
instance obj_injective (M : ModuleCat.{max u v} R) :
    Injective (obj R M) := sorry
/- Proof strategy: use `Module.injective_iff_injective_object` and
`injective R M`. -/

/-- The explicit target and embedding give an injective presentation of
`M`. -/
@[stacks 01DD "explicit character-module injective presentation"]
noncomputable def presentation (M : ModuleCat.{max u v} R) :
    InjectivePresentation M where
  J := obj R M
  injective := obj_injective R M
  f := ιApp R M
  mono := mono_ιApp R M

/-- Lemma 15.55.9, tag `01DD`: the explicit character-module construction
supplies functorial injective embeddings. This is a named value rather than a
global instance, so consumers can choose it without changing ambient instance
search. -/
@[stacks 01DD "character-module functorial injective embeddings", reducible]
noncomputable def functorialInjectives :
    HasFunctorialInjectives (ModuleCat.{max u v} R) where
  functor := functor R
  ι := ι R
  mono_app := mono_ιApp R
  injective_obj := obj_injective R

end CharacterModule.Resolution
