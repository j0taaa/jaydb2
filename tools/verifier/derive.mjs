import { createHash } from 'node:crypto';

export const LEAN_VERSION = '4.34.0';
export const sha256 = bytes => createHash('sha256').update(bytes).digest('hex');

function replaceOnce(text, before, after) {
  if (text.split(before).length !== 2) throw new Error('Pinned BendTT derivation anchor changed: ' + before.slice(0, 80));
  return text.replace(before, after);
}

/** Keep every logical rule and proof; generalize only the execution budget. */
export function deriveKernel(original) {
  let text = replaceOnce(original, 'def FUEL : Nat := 400000000', `class FuelBudget where
  amount : Nat

def FUEL [FuelBudget] : Nat := FuelBudget.amount`);
  text = replaceOnce(text, 'def Ctx.wnf (ck : Book)', `section ExecutionBudget
variable [FuelBudget]
set_option linter.unusedSectionVars false

def Ctx.wnf (ck : Book)`);
  text = replaceOnce(text, 'def main (args : List String)', 'def pinnedMain (args : List String)');

  // This second checker differs only in refusing a weak head whose reduction
  // exhausted its budget. The original checker remains the acceptance gate,
  // with all its original proofs, generalized over the FuelBudget instance.
  // In particular we do not change the pure Ctx.wnf used by those proofs.
  const start = original.indexOf('def Term.infer (ck : Book)');
  const end = original.indexOf('\nend\n', start);
  if (start < 0 || end < 0) throw new Error('Pinned bidirectional checker missing');
  let guarded = original.slice(start, end)
    .replaceAll('Res Term', 'BudgetRes Term').replaceAll('Res Unit', 'BudgetRes Unit')
    .replaceAll('Term.infer', 'Term.inferBudget').replaceAll('Term.check', 'Term.checkBudget')
    .replaceAll('Ctx.fail', 'Budget.fail').replaceAll('Ctx.fit', 'Budget.fit')
    .replaceAll('Ctx.need', 'Budget.needFuel').replaceAll('Res.need', 'Budget.need')
    .replaceAll('throw "out of fuel"', 'throw .exhausted')
    .replaceAll('throw "unbound variable"', 'throw (.invalid "unbound variable")')
    .replaceAll('throw ("unknown def: " ++ k)', 'throw (.invalid ("unknown def: " ++ k))')
    .replaceAll('Ctx.wnf', 'Ctx.wnfBudget')
    .replace(/match Ctx\.wnfBudget ck c (\w+) with/g, 'match (← Ctx.wnfBudget ck c $1) with')
    .replaceAll('let V := Ctx.wnfBudget', 'let V ← Ctx.wnfBudget')
    .replaceAll('let A := Ctx.wnfBudget', 'let A ← Ctx.wnfBudget')
    .replace(/=>\n(\s*)match \(←/g, '=> do\n$1match (←');
  const validatorStart = original.indexOf('def Def.check (bk : Book)');
  const validatorEnd = original.indexOf('\n-- Main', validatorStart);
  if (validatorStart < 0 || validatorEnd < 0) throw new Error('Pinned book checker missing');
  const validator = original.slice(validatorStart, validatorEnd)
    .replaceAll('Res Unit', 'BudgetRes Unit').replaceAll('Res.need', 'Budget.need')
    .replaceAll('Def.check', 'Def.checkBudget').replaceAll('Term.check', 'Term.checkBudget')
    .replaceAll('Book.check_from', 'Book.budgetCheckFrom').replaceAll('Book.check', 'Book.checkBudget')
    .replaceAll('.mapError (fun e => "In " ++ d.k ++ ":\\n" ++ e)',
      '.mapError (fun | .exhausted => .exhausted | .invalid e => .invalid ("In " ++ d.k ++ ":\\n" ++ e))');
  text += `

-- Resource-complete execution adapter. Acceptance still requires Book.check.
inductive BudgetError where
  | exhausted
  | invalid : String → BudgetError

abbrev BudgetRes := Except BudgetError

def Budget.fail (c : Ctx) (x : String) (o : Term) : BudgetRes α :=
  (Ctx.fail c x o).mapError BudgetError.invalid

def Budget.need (b : Bool) (e : String) : BudgetRes Unit :=
  (Res.need b e).mapError BudgetError.invalid

def Budget.needFuel (c : Ctx) (r : Bool × Nat) (x : String) (o : Term) : BudgetRes Unit :=
  match r with
  | (true, _) => pure ()
  | (_, 0) => throw .exhausted
  | _ => Budget.fail c x o

def Budget.fit (ck : Book) (c : Ctx) (U T : Term) : BudgetRes Unit :=
  let U := Ctx.zeta c U
  let T := Ctx.zeta c T
  Budget.needFuel c (Term.fits ck c.isEmpty FUEL U T) (Term.show T c.length) U

def Ctx.wnfBudget (ck : Book) (c : Ctx) (t : Term) : BudgetRes Term := do
  let r := Term.wnf ck c.isEmpty FUEL (Ctx.zeta c t) []
  if r.2 == 0 then throw .exhausted else pure r.1

mutual
${guarded}
end

${validator}

-- Quantification over FuelBudget is explicit in the generated trust report.
#check @book_check
#check @consistent
#check @adequate
#print axioms book_check
#print axioms consistent
#print axioms adequate

end ExecutionBudget

def main (args : List String) : IO UInt32 := do
  match args with
  | [path, amount] =>
    match amount.toNat? with
    | none =>
      IO.println "BENDTT INFRASTRUCTURE: invalid execution budget"
      pure 2
    | some fuel => do
      let s ← IO.FS.readFile path
      match Book.parse s with
      | .error e =>
        IO.println ("SOME PROOFS FAIL\\n" ++ e)
        pure 1
      | .ok bk =>
        match @Book.checkBudget ⟨fuel⟩ bk with
        | .error .exhausted =>
          IO.println "BENDTT BUDGET EXHAUSTED"
          pure 75
        | .error (.invalid e) =>
          IO.println ("SOME PROOFS FAIL\\n" ++ e)
          pure 1
        | .ok _ =>
          match @Book.check ⟨fuel⟩ bk with
          | .ok _ =>
            IO.println "ALL PROOFS CHECK"
            pure 0
          | .error e =>
            IO.println ("BENDTT INFRASTRUCTURE: guarded/original disagreement\\n" ++ e)
            pure 2
  | _ =>
    IO.println "usage: bendtt-budget <file.bendtt> <fuel>"
    pure 2
`;
  return text;
}
