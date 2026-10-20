module

public import ReasLib.CategoryTheory.Fibered.Fiber.Opposite
public import ReasLib.CategoryTheory.Fibered.ChosenCleavage.Basic.Coherence
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.FiberedCategory.Cocartesian
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Pushforwards from a cleavage of the opposite projection

An explicit cleavage supplies pushforward objects, cocartesian arrows, compatible
comparisons, and maps on fibre automorphisms. Selected pushforwards specialize
these constructions to the cleavage chosen from fibredness.
-/

@[expose] public section

open CategoryTheory Opposite Under

universe u₁ v₁ u₂ v₂

variable {C : Type u₁} [Category.{v₁} C]
variable {F : Type u₂} [Category.{v₂} F]

namespace CategoryTheory.Functor.Cleavage

open Fiber

variable {p : F ⥤ C}

/-- The supplied pushforward of a fibre object along a base arrow, obtained from the supplied
cleavage of `p.op`. -/
noncomputable def pushforwardObj (χ : p.op.Cleavage) {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : p.Fiber V :=
  fromOp (χ.reindexObj f.op (toOp x))

/-- The supplied cocartesian lift `x ⟶ f_* x`, as the unopposite of the supplied cartesian arrow
of `p.op`. -/
noncomputable def pushforwardHom (χ : p.op.Cleavage) {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : x.1 ⟶ (pushforwardObj χ f x).1 :=
  (χ.cartesianHom f.op (toOp x)).unop

/-- The supplied pushforward arrow is strongly cocartesian over its base arrow. -/
theorem pushforwardHom_isStronglyCocartesian (χ : p.op.Cleavage)
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    p.IsStronglyCocartesian f (pushforwardHom χ f x) := by
  have unopLift {baseSource baseTarget : Cᵒᵖ} {source target : Fᵒᵖ}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.op.IsHomLift base arrow) :
      p.IsHomLift base.unop arrow.unop := by
    cases certificate
    exact IsHomLift.map _
  have opLift {baseSource baseTarget : C} {source target : F}
      {base : baseSource ⟶ baseTarget} {arrow : source ⟶ target}
      (certificate : p.IsHomLift base arrow) :
      p.op.IsHomLift base.op arrow.op := by
    cases certificate
    exact IsHomLift.map _
  have certificate := (χ.reindexLift f.op (toOp x)).isStronglyCartesian
  refine { toIsHomLift := unopLift certificate.toIsHomLift
           universal_property' := ?_ }
  intro target base arrow arrowLift
  have oppositeLift : p.op.IsHomLift (base.op ≫ f.op) arrow.op := by
    simpa only [op_comp] using opLift arrowLift
  obtain ⟨factor, ⟨factorLift, factorization⟩, uniqueness⟩ :=
    @IsStronglyCartesian.universal_property' _ _ _ _ p.op _ _ _ _
      f.op (χ.cartesianHom f.op (toOp x)) certificate
      (op target) base.op arrow.op oppositeLift
  refine ⟨factor.unop, ⟨unopLift factorLift, ?_⟩, ?_⟩
  · exact congrArg Quiver.Hom.unop factorization
  · intro candidate candidateProperty
    apply Quiver.Hom.op_inj
    exact uniqueness candidate.op
      ⟨opLift candidateProperty.1, congrArg Quiver.Hom.op candidateProperty.2⟩

/-- The supplied pushforward arrow lies over its displayed base arrow. -/
theorem pushforwardHom_isHomLift (χ : p.op.Cleavage) {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    p.IsHomLift f (pushforwardHom χ f x) := sorry

/-- The supplied comparison isomorphism in the opposite fibre for a specified composite
`f.hom ≫ φ.right = g.hom`. -/
noncomputable def pushforwardCompIso (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    χ.reindexObj g.hom.op (toOp x) ≅
      χ.reindexObj φ.right.op (χ.reindexObj f.hom.op (toOp x)) :=
  Reindex.specifiedCompIsoApp χ f.hom.op φ.right.op g.hom.op
    (op_comp.symm.trans (congrArg Quiver.Hom.op (Under.w φ))) (toOp x)

/-- The unique comparison `f_* x ⟶ g_* x` over an under-morphism `φ`, compatible with the two
supplied pushforward arrows from `x`. -/
noncomputable def pushforwardComparison (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    (pushforwardObj χ f.hom x).1 ⟶ (pushforwardObj χ g.hom x).1 :=
  ((pushforwardCompIso χ φ x).hom.1 ≫
      χ.cartesianHom φ.right.op (χ.reindexObj f.hom.op (toOp x))).unop

/-- The supplied comparison arrow lies over the under-morphism's base arrow. -/
theorem pushforwardComparison_isHomLift (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    p.IsHomLift φ.right (pushforwardComparison χ φ x) := sorry

/-- The supplied comparison arrow is compatible with the two pushforward arrows from `x`. -/
theorem pushforwardComparison_fac (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardHom χ f.hom x ≫ pushforwardComparison χ φ x =
      pushforwardHom χ g.hom x := sorry

/-- A comparison over `φ.right` compatible with the two supplied pushforward arrows is the
supplied comparison. -/
theorem pushforwardComparison_unique (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U)
    (ψ : (pushforwardObj χ f.hom x).1 ⟶ (pushforwardObj χ g.hom x).1)
    (hψ : p.IsHomLift φ.right ψ)
    (hfac : pushforwardHom χ f.hom x ≫ ψ = pushforwardHom χ g.hom x) :
    ψ = pushforwardComparison χ φ x := sorry

/-- The homomorphism `Aut(f_* x) → Aut(g_* x)` induced by the supplied comparison of an
under-morphism. -/
noncomputable def pushforwardAut (χ : p.op.Cleavage) {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    Aut (pushforwardObj χ f.hom x) → Aut (pushforwardObj χ g.hom x) :=
  fun α ↦
    let yf := χ.reindexObj f.hom.op (toOp x)
    let αop := Aut.autMulEquivOfIso (toOpFromOpIso yf) (toOpAut α)
    let αreindex := mapAut yf (χ.reindex φ.right.op) αop
    fromOpAut ((Aut.autMulEquivOfIso (pushforwardCompIso χ φ x)).symm αreindex)

/-- The supplied comparison conjugates a fibre automorphism to its pushforward. -/
theorem pushforwardAut_fac (χ : p.op.Cleavage) {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α : Aut (pushforwardObj χ f.hom x)) :
    pushforwardComparison χ φ x ≫ (pushforwardAut χ φ x α).hom.1 =
      α.hom.1 ≫ pushforwardComparison χ φ x := sorry

/-- Pushforward of fibre automorphisms preserves multiplication. -/
theorem pushforwardAut_mul (χ : p.op.Cleavage) {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α β : Aut (pushforwardObj χ f.hom x)) :
    pushforwardAut χ φ x (α * β) = pushforwardAut χ φ x α * pushforwardAut χ φ x β := sorry

/-- Pushforward of fibre automorphisms preserves the identity. -/
theorem pushforwardAut_one (χ : p.op.Cleavage) {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardAut χ φ x 1 = 1 := sorry

/-- Pushforward of automorphisms along an identity under-morphism is the identity map. -/
theorem pushforwardAut_id (χ : p.op.Cleavage) {U : C} (f : Under U) (x : p.Fiber U) :
    TypeCat.ofHom (pushforwardAut χ (𝟙 f) x) =
      𝟙 (Aut (pushforwardObj χ f.hom x)) := sorry

/-- Pushforward of automorphisms along a composite under-morphism is the composite map. -/
theorem pushforwardAut_comp (χ : p.op.Cleavage) {U : C} {f g h : Under U}
    (φ : f ⟶ g) (ψ : g ⟶ h) (x : p.Fiber U) :
    TypeCat.ofHom (pushforwardAut χ (φ ≫ ψ) x) =
      TypeCat.ofHom (pushforwardAut χ φ x) ≫ TypeCat.ofHom (pushforwardAut χ ψ x) := sorry

end CategoryTheory.Functor.Cleavage

namespace CategoryTheory.Functor.Chosen

open Fiber

/-- The selected pushforward of a fibre object along a base arrow, obtained from the chosen
cleavage of `p.op`. -/
noncomputable def pushforwardObj (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : p.Fiber V :=
  Cleavage.pushforwardObj (Cleavage.ofIsFibered p.op) f x

/-- The selected pushforward lies in the fibre over the codomain of its base arrow. -/
theorem pushforwardObj_property (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    p.obj (pushforwardObj p f x).1 = V := sorry

/-- The selected pushforward object is the unopposite of the chosen reindexing of `p.op`. -/
theorem pushforwardObj_eq_fromOp (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    pushforwardObj p f x = fromOp (reindexObj p.op f.op (toOp x)) := sorry

/-- The selected cocartesian lift `x ⟶ f_* x`, as the unopposite of the chosen cartesian arrow
of `p.op`. -/
noncomputable def pushforwardHom (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) : x.1 ⟶ (pushforwardObj p f x).1 :=
  Cleavage.pushforwardHom (Cleavage.ofIsFibered p.op) f x

/-- The selected pushforward arrow satisfies the strongly cocartesian universal property
over its base arrow. -/
private theorem pushforwardHom_stronglyCocartesian (p : F ⥤ C) [p.op.IsFibered]
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    p.IsStronglyCocartesian f (pushforwardHom p f x) :=
  Cleavage.pushforwardHom_isStronglyCocartesian (Cleavage.ofIsFibered p.op) f x

/-- The selected pushforward arrow is strongly cocartesian over its base arrow. -/
instance pushforwardHom.isStronglyCocartesian (p : F ⥤ C) [p.op.IsFibered]
    {U V : C} (f : U ⟶ V) (x : p.Fiber U) :
    p.IsStronglyCocartesian f (pushforwardHom p f x) :=
  pushforwardHom_stronglyCocartesian p f x

/-- The selected pushforward arrow lies over its displayed base arrow. -/
theorem pushforwardHom_isHomLift (p : F ⥤ C) [p.op.IsFibered] {U V : C} (f : U ⟶ V)
    (x : p.Fiber U) :
    p.IsHomLift f (pushforwardHom p f x) := sorry

/-- The selected comparison isomorphism in the opposite fibre for a specified composite
`f.hom ≫ φ.right = g.hom`. -/
noncomputable def pushforwardCompIso (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    reindexObj p.op g.hom.op (toOp x) ≅
      reindexObj p.op φ.right.op (reindexObj p.op f.hom.op (toOp x)) :=
  Cleavage.pushforwardCompIso (Cleavage.ofIsFibered p.op) φ x

/-- The selected comparison isomorphism is the specified-composite comparison of `p.op`. -/
theorem pushforwardCompIso_eq_specifiedCompIsoApp (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardCompIso p φ x =
      Reindex.specifiedCompIsoApp p.op f.hom.op φ.right.op g.hom.op
        (op_comp.symm.trans (congrArg Quiver.Hom.op (Under.w φ))) (toOp x) := sorry

/-- The unique comparison `f_* x ⟶ g_* x` over an under-morphism `φ`, compatible with the two
selected pushforward arrows from `x`. -/
noncomputable def pushforwardComparison (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    (pushforwardObj p f.hom x).1 ⟶ (pushforwardObj p g.hom x).1 :=
  Cleavage.pushforwardComparison (Cleavage.ofIsFibered p.op) φ x

/-- The selected comparison arrow lies over the under-morphism's base arrow. -/
theorem pushforwardComparison_isHomLift (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    p.IsHomLift φ.right (pushforwardComparison p φ x) := sorry

/-- The selected comparison arrow is compatible with the two pushforward arrows from `x`. -/
theorem pushforwardComparison_fac (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardHom p f.hom x ≫ pushforwardComparison p φ x =
      pushforwardHom p g.hom x := sorry

/-- A comparison over `φ.right` compatible with the two selected pushforward arrows is the
selected comparison. -/
theorem pushforwardComparison_unique (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U)
    (ψ : (pushforwardObj p f.hom x).1 ⟶ (pushforwardObj p g.hom x).1)
    (hψ : p.IsHomLift φ.right ψ)
    (hfac : pushforwardHom p f.hom x ≫ ψ = pushforwardHom p g.hom x) :
    ψ = pushforwardComparison p φ x := sorry

/-- The homomorphism `Aut(f_* x) → Aut(g_* x)` induced by the selected comparison of an
under-morphism. -/
noncomputable def pushforwardAut (p : F ⥤ C) [p.op.IsFibered] {U : C}
    {f g : Under U} (φ : f ⟶ g) (x : p.Fiber U) :
    Aut (pushforwardObj p f.hom x) → Aut (pushforwardObj p g.hom x) :=
  Cleavage.pushforwardAut (Cleavage.ofIsFibered p.op) φ x

/-- The selected comparison conjugates a fibre automorphism to its pushforward. -/
theorem pushforwardAut_fac (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α : Aut (pushforwardObj p f.hom x)) :
    pushforwardComparison p φ x ≫ (pushforwardAut p φ x α).hom.1 =
      α.hom.1 ≫ pushforwardComparison p φ x := sorry

/-- Pushforward of fibre automorphisms preserves multiplication. -/
theorem pushforwardAut_mul (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) (α β : Aut (pushforwardObj p f.hom x)) :
    pushforwardAut p φ x (α * β) = pushforwardAut p φ x α * pushforwardAut p φ x β := sorry

/-- Pushforward of fibre automorphisms preserves the identity. -/
theorem pushforwardAut_one (p : F ⥤ C) [p.op.IsFibered] {U : C} {f g : Under U}
    (φ : f ⟶ g) (x : p.Fiber U) :
    pushforwardAut p φ x 1 = 1 := sorry

end CategoryTheory.Functor.Chosen
