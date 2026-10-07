module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Quasicoherent
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper.FiniteUnion
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType

/-!
# Proper support of scheme modules

This file packages the topological closure of a module support as a closed subset and records
properness of finite-type quasi-coherent support under base change and the standard abelian
operations.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The closed support of a module on a scheme is the topological closure of its module support. -/
def closedSupport {X : Scheme.{u}} (ℱ : X.Modules) : TopologicalSpace.Closeds X :=
  TopologicalSpace.Closeds.closure (moduleSupport ℱ)

/-- The underlying set of the closed support is the module support. -/
@[simp]
theorem coe_closedSupport {X : Scheme.{u}} (ℱ : X.Modules)
    [ℱ.IsFiniteType] :
    (closedSupport ℱ : Set X) = moduleSupport ℱ := by
  rw [closedSupport, TopologicalSpace.Closeds.coe_closure,
    (isClosed_moduleSupport ℱ).closure_eq]

/-- Pullback carries the closed support of a finite-type quasi-coherent module to its inverse
image. -/
theorem closedSupport_pullback
    {X Y : Scheme.{u}} (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    (f : Y ⟶ X) :
    closedSupport ((Scheme.Modules.pullback f).obj ℱ) =
      (closedSupport ℱ).preimage f.continuous := sorry

/-- In a cartesian square, pullback preserves properness over the base of the closed support of a
finite-type quasi-coherent module. -/
theorem closedSupport_pullback_isProperOver
    {X' X S' S : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ S'}
    {f : X ⟶ S} {g : S' ⟶ S} (sq : IsPullback g' f' f g)
    [LocallyOfFiniteType f] (ℱ : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport ℱ)] :
    ClosedSubset.IsProperOver f' (closedSupport ((Scheme.Modules.pullback g').obj ℱ)) := sorry

/-- A module on `X` has proper support over `f : X ⟶ S` when its support is closed and the
corresponding reduced closed subscheme is proper over `S`. -/
class HasProperSupportOver {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules) : Prop where
  /-- The support of the module is closed. -/
  isClosed_moduleSupport : IsClosed (moduleSupport ℱ)
  /-- The reduced closed subscheme on the support is proper over the base. -/
  isProper_moduleSupport :
    ClosedSubset.IsProperOver f
      (⟨moduleSupport ℱ, isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X)

/-- A finite-type module has proper support when its canonical closed support is proper. -/
instance instHasProperSupportOverOfClosedSupportIsProper
    {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
    [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [ClosedSubset.IsProperOver f (closedSupport ℱ)] :
    HasProperSupportOver f ℱ :=
  ⟨isClosed_moduleSupport ℱ, by
    have h :
        (⟨moduleSupport ℱ, isClosed_moduleSupport ℱ⟩ : TopologicalSpace.Closeds X) =
          closedSupport ℱ := by
      apply SetLike.coe_injective
      exact (coe_closedSupport ℱ).symm
    rw [h]
    infer_instance⟩

/-- Proper support gives properness of the reduced closed subscheme on the module support. -/
theorem HasProperSupportOver.isProper
    {X S : Scheme.{u}} {f : X ⟶ S} {ℱ : X.Modules} [h : HasProperSupportOver f ℱ] :
    ClosedSubset.IsProperOver f
      (⟨moduleSupport ℱ, h.isClosed_moduleSupport⟩ : TopologicalSpace.Closeds X) :=
  h.isProper_moduleSupport

/-- Having proper support is equivalent to closedness of the support together with properness of
its reduced closed subscheme over the base. -/
theorem hasProperSupportOver_iff
    {X S : Scheme.{u}} {f : X ⟶ S} {ℱ : X.Modules} :
    HasProperSupportOver f ℱ ↔
      ∃ hclosed : IsClosed (moduleSupport ℱ),
        ClosedSubset.IsProperOver f
          (⟨moduleSupport ℱ, hclosed⟩ : TopologicalSpace.Closeds X) := sorry

/-- A finite-type quasi-coherent module whose support is contained in a proper module support
also has proper support. -/
theorem HasProperSupportOver.of_subset
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ℱ 𝒢 : X.Modules} [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [HasProperSupportOver f 𝒢]
    (h : moduleSupport ℱ ⊆ moduleSupport 𝒢) :
    HasProperSupportOver f ℱ := sorry

/-- The biproduct of two finite-type quasi-coherent modules with proper support has proper
support. -/
theorem HasProperSupportOver.biprod
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢] :
    HasProperSupportOver f (ℱ ⊞ 𝒢) := sorry

/-- In a short exact sequence of finite-type quasi-coherent modules, proper support of the outer
terms implies proper support of the middle term. -/
theorem HasProperSupportOver.middle_of_shortExact
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (C : ShortComplex X.Modules)
    [C.X₁.IsFiniteType] [C.X₁.IsQuasicoherent]
    [C.X₃.IsFiniteType] [C.X₃.IsQuasicoherent]
    [HasProperSupportOver f C.X₁] [HasProperSupportOver f C.X₃]
    (hC : C.ShortExact) :
    HasProperSupportOver f C.X₂ := sorry

/-- A quasi-coherent quotient of a finite-type quasi-coherent module with proper support has
proper support. -/
theorem HasProperSupportOver.of_epi
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    {ℱ Q : X.Modules} [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [Q.IsQuasicoherent] [HasProperSupportOver f ℱ]
    (q : ℱ ⟶ Q) [Epi q] :
    HasProperSupportOver f Q := sorry

/-- The image of a morphism between finite-type quasi-coherent modules with proper support has
proper support. -/
theorem HasProperSupportOver.image
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (Abelian.image u) := sorry

/-- The cokernel of a morphism between finite-type quasi-coherent modules with proper support has
proper support. -/
theorem HasProperSupportOver.cokernel
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (ℱ 𝒢 : X.Modules) [ℱ.IsFiniteType] [ℱ.IsQuasicoherent]
    [𝒢.IsFiniteType] [𝒢.IsQuasicoherent]
    [HasProperSupportOver f ℱ] [HasProperSupportOver f 𝒢]
    (u : ℱ ⟶ 𝒢) :
    HasProperSupportOver f (cokernel u) := sorry

/-- On a scheme locally of finite type over a locally Noetherian base, coherent modules with
proper support form a Serre class. -/
instance coherent_hasProperSupportOver_isSerreClass
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    [AlgebraicGeometry.IsLocallyNoetherian S] :
    ObjectProperty.IsSerreClass
      ((fun ℱ : RingedSpace.Coh X.toRingedSpace ↦ HasProperSupportOver f ℱ.obj) :
        ObjectProperty (RingedSpace.Coh X.toRingedSpace)) := sorry

end AlgebraicGeometry.Scheme.Modules
