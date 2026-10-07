module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Equivalence.Basic
public import stacks_project.Chap90.Lemma_90_7_4

/-!
# Completion along a family of maximal-adic equivalent filtrations

Objects of `hat F_I` are a complete local base together with a formal object of
`p` along the supplied filtration of that base. The projection to
`CompleteLocalAlgCat` is cofibered in groupoids, each fibre is equivalent to
the corresponding `Along` fibre, and the comparison to ordinary completion is
an equivalence over the completed base.
-/

@[expose] public section

open CategoryTheory CompleteLocalAlgCat
open scoped BasedFunctor

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

namespace FormalObject

/-- An object of the total category `hat F_I`: a complete local algebra together
with an inverse system of `p` along the supplied filtration of that algebra. -/
structure AlongOver (p : F ⥤ ArtinianLocalAlgCat Λ k)
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R) where
  /-- Complete local base of the object. -/
  base : CompleteLocalAlgCat Λ k
  /-- Inverse system of `p` along the filtration of `base`. -/
  along : Along p base (I base)

namespace AlongOver

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}

/-- Package a complete local algebra and an inverse system along its filtration. -/
def of (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) : AlongOver p I where
  base := R
  along := ξ

/-- The base of a packaged object is the supplied complete local algebra. -/
theorem of_base (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    (of I R ξ).base = R := sorry

/-- The stored inverse system of a packaged object is the supplied `Along` object. -/
theorem of_along (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    (of I R ξ).along = ξ := sorry

/-- Stagewise specification of an object of `hat F_I` over the truncations of its
filtration. -/
theorem spec {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
    (ξ : AlongOver p I) (n : ℕ) :
    p.obj (ξ.along.system.family n) = (I ξ.base).truncation n ∧
      p.IsHomLift ((I ξ.base).truncationMap n) (ξ.along.system.stepMap n) := sorry

variable {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
variable [Functor.IsFibered.InGroupoids p.op]

/-- The ordinary formal object obtained by pushing the stored `I`-system along
maximal-adic comparisons. -/
noncomputable def toFormalObject (ξ : AlongOver p I) : FormalObject p :=
  ξ.along.toFormalObject

/-- Pushing an object of `hat F_I` recovers the stored `Along` system after the
maximal-adic comparison of Lemma 90.7.4. -/
theorem toFormalObject_eq (ξ : AlongOver p I) :
    toFormalObject ξ = ξ.along.toFormalObject := sorry

/-- Morphisms of `hat F_I` are morphisms of the pushed maximal-adic systems. -/
noncomputable instance category : Category.{max u v} (AlongOver p I) where
  Hom ξ η := ξ.along.toFormalObject ⟶ η.along.toFormalObject
  id ξ := 𝟙 ξ.along.toFormalObject
  comp f g := f ≫ g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The comparison functor `hat F_I ⥤ hat F` sending each `I`-system to the
pushed maximal-adic formal object. -/
noncomputable def toCompletion (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    AlongOver p I ⥤ FormalObject p where
  obj ξ := ξ.along.toFormalObject
  map a := a
  map_id := sorry
  map_comp := sorry

/-- The comparison functor sends an object of `hat F_I` to the pushed formal
object of its stored `Along` system. -/
theorem toCompletion_obj (ξ : AlongOver p I) :
    (toCompletion I p).obj ξ = ξ.along.toFormalObject := sorry

end AlongOver

end FormalObject

namespace CategoryTheory.Functor

/-- The projection `hat p_I : hat F_I ⥤ hat C_Λ` sending an object of
`FormalObject.AlongOver p I` to its complete local base. -/
noncomputable def completionAlong
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op] :
    FormalObject.AlongOver p I ⥤ CompleteLocalAlgCat Λ k :=
  FormalObject.AlongOver.toCompletion I p ⋙ completion p

/-- The projection `hat p_I` sends an object to its complete local base. -/
theorem completionAlong_obj
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    (ξ : FormalObject.AlongOver p I) :
    (completionAlong I p).obj ξ = ξ.base := sorry

/-- The projection `hat p_I` sends a morphism to its complete local base map. -/
theorem completionAlong_map
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [IsFibered.InGroupoids p.op]
    {ξ η : FormalObject.AlongOver p I} (a : ξ ⟶ η) :
    (completionAlong I p).map a = a.base := sorry

end CategoryTheory.Functor

namespace FormalObject.AlongOver

variable {p : F ⥤ ArtinianLocalAlgCat Λ k}
variable {I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R}
variable [Functor.IsFibered.InGroupoids p.op]

/-- The comparison `hat F_I ⥤ hat F` lies strictly over the identity of
`CompleteLocalAlgCat Λ k`. -/
theorem toCompletion_comp :
    toCompletion I p ⋙ Functor.completion p = Functor.completionAlong I p := sorry

/-- The fibre identification `hat F_{I R}(R) ⥤ hat F_I(R)` sending an inverse
system along `I R` to the corresponding object of the total category. -/
noncomputable def ofAlong (p : F ⥤ ArtinianLocalAlgCat Λ k)
    [Functor.IsFibered.InGroupoids p.op]
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) :
    Along p R (I R) ⥤ Functor.Fiber (Functor.completionAlong I p) R where
  obj ξ := ⟨of I R ξ, rfl⟩
  map a := ⟨Along.toFormalObjectMap a, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The fibre identification sends an `Along` object to the packaged object of
`hat F_I` over `R`. -/
theorem ofAlong_obj (R : CompleteLocalAlgCat Λ k) (ξ : Along p R (I R)) :
    Functor.Fiber.fiberInclusion.obj ((ofAlong p I R).obj ξ) = of I R ξ := sorry

/-- The comparison `hat F_I ⥤ hat F` as a based functor over `hat C_Λ`. -/
noncomputable def toCompletionBased
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    BasedCategory.ofFunctor (Functor.completionAlong I p) ⥤ᵇ
      BasedCategory.ofFunctor (Functor.completion p) where
  toFunctor := toCompletion I p
  w := rfl

/-- The underlying functor of the based comparison is `toCompletion`. -/
theorem toCompletionBased_toFunctor :
    (toCompletionBased I p).toFunctor = toCompletion I p := sorry

end FormalObject.AlongOver

end
