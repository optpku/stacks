/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder.Decomposition
public import ReasLib.Algebra.Module.PrincipalParts.FirstOrder.Truncation
public import ReasLib.Algebra.Module.PrincipalParts.Diagonal
public import ReasLib.Algebra.Module.PrincipalParts.TensorProduct
public import ReasLib.Algebra.Module.PrincipalParts.FormallyEtale
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.BaseChange.Truncation
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.ZerothOrder
public import ReasLib.Algebra.Module.PrincipalParts.RingHom.FirstOrder

/-!
# Principal Parts

This is the algebraic family entry point for principal-parts modules, their
universal property, truncation and base-change maps, and the zeroth- and
first-order comparison APIs.  Presheaf and sheaf constructions remain
opt-in leaves above this layer.

@stack 09CK
@stack 09CL
@stack 09CN
@stack 09CP
-/
