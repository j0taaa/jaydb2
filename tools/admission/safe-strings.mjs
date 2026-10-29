// Only the serializer changes: the checked Book and the independent kernel
// remain identical. Base String.append denotes concatenation of the same
// constructor chains. Balanced splitting bounds call depth by log(length),
// without a maximum string length or cutting a Unicode scalar in half.
export function adaptSafeStrings(source) {
  const anchor = '    case "Lit": {\n      if (x.k === "Nat"';
  if (source.split(anchor).length !== 2) throw new Error('Safe strings: upstream anchor diverged');
  const replacement = `    case "Lit": {
      if (x.k === "String" && x.v.length > 64 && e.book.tlds.String?.b === true
          && e.book.tlds["String.append"]?.b === true) {
        let at = Math.floor(x.v.length / 2);
        const previous = x.v.charCodeAt(at - 1), current = x.v.charCodeAt(at);
        if (previous >= 0xd800 && previous <= 0xdbff && current >= 0xdc00 && current <= 0xdfff) at++;
        const joined = B.App(B.App(B.Ref("String.append"), B.Lit("String", x.v.slice(0, at))),
          B.Lit("String", x.v.slice(at)));
        return term(e, s, joined, live);
      }
      if (x.k === "Nat"`;
  return source.replace(anchor, replacement);
}
