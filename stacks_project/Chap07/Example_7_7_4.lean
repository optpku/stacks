/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.Topology.Category.TopCat.GenericPoint

@[expose] public section

/-
Example 7.7.4: adjoining a generic point to `X` produces the space
`TopCat.GenericPoint.extension X`, whose nonempty opens are the basic opens
`U ∪ {none}`. Its opens basis presents the corresponding modified site.
-/
@[stacks 00VP] #check @TopCat.GenericPoint.extension

@[stacks 00VP "inclusion into the generic-point extension"]
#check @TopCat.GenericPoint.inclusion
@[stacks 00VP "basis of opens after adjoining the generic point"]
#check @TopCat.GenericPoint.basis
@[stacks 00VP "covering-family characterization on the modified opens site"]
#check @TopCat.GenericPoint.Opens.covering_iff_mem_topology
@[stacks 00VP "comparison equivalence for sheaves on the modified site"]
#check @TopCat.GenericPoint.Opens.sheafEquiv
@[stacks 00VP "set-valued sheaf comparison equivalence"]
#check @TopCat.GenericPoint.Opens.typeSheafEquiv
