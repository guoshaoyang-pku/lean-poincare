/-
Copyright (c) 2026 The Poincaré formalization program. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Poincaré project (D7-surgery-neck-extinction)

**D7 surgery flow: umbrella module.**

This module imports the four layers of the surgery/neck/extinction interface:

* `Poincare.D7.SurgeryFlow.Basic` — surgery procedure data consuming canonical neighborhoods,
  extending the D3 surgery ledger;
* `Poincare.D7.SurgeryFlow.Times` — discreteness of the surgery times under the stated
  curvature-bound interface;
* `Poincare.D7.SurgeryFlow.Extinction` — extinction for the finite toy complexity relation,
  reusing the D3 `ToyRel` results;
* `Poincare.D7.SurgeryFlow.Statements` — the state-only Props (full neck analysis, a-priori
  curvature estimates, extinction theorem) with the named missing-input ledger.
-/

import Poincare.D7.SurgeryFlow.Basic
import Poincare.D7.SurgeryFlow.Times
import Poincare.D7.SurgeryFlow.Extinction
import Poincare.D7.SurgeryFlow.Statements
