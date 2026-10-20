module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Limits.HasLimits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.MorphismBaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute.Relative

/-!
# Separatedness descent along directed affine limits of algebraic spaces

If a specified inverse limit of quasi-compact, absolutely quasi-separated algebraic
spaces with affine transitions is absolutely separated, then all sufficiently late
stages are absolutely separated. Over a quasi-separated algebraic space, separatedness
of the compatible limit morphism likewise implies separatedness of all sufficiently
late stage morphisms.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Limit

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms, if a specified limit is
absolutely separated, then all sufficiently late stages are absolutely
separated. -/
theorem exists_eventually_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [IsAbsolutelySeparated c.pt] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → IsAbsolutelySeparated (D.obj i) := sorry

/-- If a specified inverse limit of quasi-compact and absolutely quasi-separated
algebraic spaces with affine transition morphisms is absolutely separated, then
some stage is absolutely separated. -/
theorem exists_isSeparated_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
    (c : Cone D) (hc : IsLimit c)
    [∀ j, IsQuasiCompact (D.obj j)]
    [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
    [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
    [IsAbsolutelySeparated c.pt] :
    ∃ i : I, IsAbsolutelySeparated (D.obj i) := by
  obtain ⟨i₀, hi₀⟩ := exists_eventually_isSeparated_of_isLimit D c hc
  exact ⟨i₀, hi₀ le_rfl⟩

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces over an absolutely quasi-separated base, with affine transition
morphisms, separatedness of the compatible limit morphism implies separatedness
of every sufficiently late stage morphism. -/
theorem exists_eventually_isSeparated_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Separated σlim] :
    ∃ i₀ : I, ∀ ⦃i : I⦄, i₀ ≤ i → Separated (t.app i) := sorry

/-- In a directed inverse system of quasi-compact and absolutely quasi-separated
algebraic spaces over an absolutely quasi-separated base, with affine transition
morphisms, separatedness of the compatible limit morphism implies separatedness
of some stage morphism. -/
theorem exists_isSeparated_to_base_of_isLimit
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {Y : AlgebraicSpace S}
    (D : OrderDual I ⥤ AlgebraicSpace S)
    (t : D ⟶ (Functor.const (OrderDual I)).obj Y)
    (c : Cone D) (hc : IsLimit c) (σlim : c.pt ⟶ Y)
    (hπ : c.π ≫ t = (Functor.const _).map σlim)
    [IsAbsolutelyQuasiSeparated Y]
    [∀ i : I, IsQuasiCompact (D.obj i)]
    [∀ i : I, IsAbsolutelyQuasiSeparated (D.obj i)]
    [∀ {i i' : I} (hii' : i ≤ i'), Affine (D.map (homOfLE hii'))]
    [Separated σlim] :
    ∃ i : I, Separated (t.app i) := by
  obtain ⟨i₀, hi₀⟩ :=
    exists_eventually_isSeparated_to_base_of_isLimit D t c hc σlim hπ
  exact ⟨i₀, hi₀ le_rfl⟩

namespace QcqsMorphismBaseChange

/-- For a morphism between quasi-compact and absolutely quasi-separated algebraic
spaces over a quasi-compact and absolutely quasi-separated distinguished stage of
a directed inverse system with affine transitions, separatedness after base change
to the specified limit implies separatedness after base change to some stage
above the distinguished stage. -/
theorem exists_separated_stage_of_limitHom
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S} {i0 : I}
    {X0 Y0 : AlgebraicSpace S}
    [IsQuasiCompact (D.obj i0)] [IsAbsolutelyQuasiSeparated (D.obj i0)]
    [IsQuasiCompact X0] [IsAbsolutelyQuasiSeparated X0]
    [IsQuasiCompact Y0] [IsAbsolutelyQuasiSeparated Y0]
    [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
    (s : QcqsMorphismBaseChange D i0 X0 Y0) (h_limit : Separated s.limitHom) :
    ∃ (i : I) (hi0i : i0 ≤ i), Separated (s.stageHom i hi0i) := sorry

end QcqsMorphismBaseChange

end AlgebraicGeometry.AlgebraicSpace.Limit
