import {
  arrayFindIndex,
  arrayIncludes,
  arraySlice,
  freeze,
  freezeClass,
  freezeRecord as rec,
} from '@bablr/agast-helpers/object';
import { get, getRoot, list } from '@bablr/agast-helpers/path';
import * as BSet from '@bablr/agast-helpers/b-set';
import * as BMap from '@bablr/agast-helpers/b-map';
import * as BListKeyed from '@bablr/agast-helpers/b-list-keyed';
import {
  defineAttribute,
  eat,
  eatMatch,
  endSpan,
  fail,
  m,
  match,
  o,
  r,
  shift,
  shiftMatch,
  startSpan,
  startSubspan,
} from '@bablr/helpers/grammar';
import { printSource } from '@bablr/agast-helpers/tree';
import { printSource as printStreamSource, printString } from '@bablr/agast-helpers/stream';
import { writePattern, writeRegexGroup } from '@bablr/helpers/builders';
import { arrayValues, flatMap, isEmpty } from '@bablr/agast-helpers/iterable';
import { triviaEnhancer } from '@bablr/helpers/trivia';
import Space from '@bablr/language-en-blank-space';
import { buildEmbeddedRegexMatcher } from '@bablr/agast-vm-helpers/builders';

let { entry } = BMap;

export const startsIdentifierPattern = String.raw`/[a-zA-Z_]/`;

let reservedWords = rec([
  'False',
  'None',
  'True',
  'and',
  'as',
  'assert',
  'async',
  'await',
  'break',
  'class',
  'continue',
  'def',
  'del',
  'elif',
  'else',
  'except',
  'finally',
  'for',
  'from',
  'global',
  'if',
  'import',
  'in',
  'is',
  'lambda',
  'nonlocal',
  'not',
  'or',
  'pass',
  'raise',
  'return',
  'try',
  'while',
  'with',
  'yield',
]);

export const escapables = freeze({
  b: '\b',
  f: '\f',
  n: '\n',
  r: '\r',
  t: '\t',
  0: '\0',
  '\\': '\\',
  '/': '/',
});

let productions = {
  if: m`<IfStatement />`,
  while: m`<While />`,
  match: m`<Match />`,
  for: m`<ForStatement />`,
  def: m`<FunctionDefinition />`,
  try: m`<TryCatch />`,
  return: m`<ReturnStatement />`,
  continue: m`<Continue />`,
  break: m`<Break />`,
  raise: m`<RaiseStatement />`,
  pass: m`<PassStatement />`,
  del: m`<DeleteStatement />`,
  yield: m`<YieldStatement />`,
  await: m`<AwaitStatement />`,
  '\r': m`<EmptyStatement />`,
  '\n': m`<EmptyStatement />`,
};

let clauses = {
  if: m`<IfClause />`,
  elif: m`<ElifClause />`,
  else: m`<ElseClause />`,
  for: m`<ForClause />`,
};

let powers = rec({
  assign: 11,
  logical_or: 10,
  logical_and: 9,
  logical_not: 8,
  compare: 7,
  bitwise_or: 6,
  bitwise_xor: 5,
  bitwise_and: 4,
  bitwise_shift: 3,
  add: 2,
  multiply: 1,
  exponent: 0,
});

function* range(start, end) {
  for (let i = start; i < end; i++) {
    yield i;
  }
}

const buildOperatorAlternatives = (categories) =>
  rec([...flatMap((operators) => arrayValues(operators), arrayValues(categories))]);

export const assignmentOperators = rec([
  '=',
  '+=',
  '-=',
  '*=',
  '/=',
  '%=',
  '<<=',
  '>>=',
  '&=',
  '^=',
  '|=',
]);
export const assignmentOperatorAlternatives = buildOperatorAlternatives([assignmentOperators]);

export const getBinaryOperatorAlternatives = (powers, power) => {
  return buildOperatorAlternatives(
    arraySlice(binaryExpressionPowerRank, Math.max(0, powers.assign - power)),
  );
};

const getBinaryOperatorPower = (p, str) => {
  let idx = arrayFindIndex(binaryExpressionPowerRank, (arr) => arrayIncludes(arr, str));
  return idx >= 0 ? p.logical_or - idx : null;
};

const binaryExpressionPowerRank = rec([
  rec(['**']),
  rec(['*', '@', '//', '/', '%']),
  rec(['+', '-']),
  rec(['<<', '>>']),
  rec(['&']),
  rec(['^']),
  rec(['|']),
  rec(['==', '!=', '<=', 'in', 'not in', 'is', 'is not', '<', '>=', '>']),
  rec(['not']),
  rec(['and']),
  rec(['or']),
  rec(['=', ':=']),
]);

export const unaryPrefixOperators = rec(['+', '-', '!', '~']);
export const unaryPrefixOperatorAlternatives = buildOperatorAlternatives([unaryPrefixOperators]);

let assignables = rec(['MemberExpression', 'Identifier']);

class PythonGrammarAtrivial {
  static canonicalURL = 'https://bablr.org/languages/universe/en/python';
  static dependencies = freeze({ Space });
  static defaultMatcher = m`_+: <_Expression />`;
  static fragmentProduction = 'Fragment';
  static context = rec({ powers, assignables });

  constructor() {
    this.literals = BSet.from('Keyword', 'Indent');
    this.emptyables = BSet.from(
      'StringContent',
      'Indent',
      'EmptyStatement',
      'StatementList',
      'Block',
    );
    this.attributes = BMap.from(entry('Dictionary', rec({ keyed: undefined })));
  }

  *Fragment({ props: { rootMatcher } }) {
    yield eat(rootMatcher);
  }

  *Module() {
    yield eat(m`<Block />`);
  }

  *StatementList({ props, s }) {
    let { indent = null } = props;

    let innerIndent = null;
    let nextIndent = null;
    while (true) {
      let first = true;
      while (yield match(m`/[ \t]*(?:[#\n\r]|$)/`)) {
        if (!first) yield eat(m`#indent: <* /[ \t]*/ />`);
        yield eatMatch(m`#: <Comment '#' />`);
        let nl = yield eatMatch(m`#: <* '\n' />`);
        if (!nl) {
          return;
        }
      }

      if (s().source.done) {
        return;
      }

      nextIndent = printSource(yield match(m`/[ \t]*/`));

      innerIndent ??= nextIndent;

      if (indent != null) {
        if (nextIndent.length <= indent.length) {
          break;
        } else if (!innerIndent.startsWith(indent)) {
          yield fail();
        }
      }

      yield match(m`#indent: <* ${printString(innerIndent)} />`);

      yield eat(m`statements[]: <_Statement />`, o({ indent: nextIndent }));
    }
  }

  *Comment() {
    yield eat(m`sigilToken: <* '#' />`);
    yield eat(m`content: <* /[^\r\n]+/ />`);
  }

  *Statement({ getState, props }) {
    let { indent = null } = props;
    let s = getState();
    let res;
    if (s.source.done) {
      return;
    } else {
      res = yield match(
        m`/(?:if|while|switch|for|def|try|return|continue|break|raise|pass|del|yield|await|[\r\n])\b/`,
      );
      yield eat(res ? productions[printSource(res)] : m`<ExpressionStatement />`, o({ indent }));
    }
  }

  *ExpressionStatement({ props }) {
    yield startSpan('Expression', '\n');
    yield eat(m`<__ExpressionList />`);
    yield endSpan();
  }

  *ExpressionList() {
    let first = true;
    let sep = null;
    while (first || sep) {
      yield eat(m`expressions[]+$: <_Expression />`);
      sep = yield eatMatch(m`#separatorToken: <* ',' />`);
      first = false;
    }
  }

  *ReturnStatement({ props }) {
    yield startSpan('Expression', '\n');
    yield eat(m`sigilToken*: <*Keyword 'return' />`);
    yield eatMatch(m`expression+$: <_Expression />`);
    yield endSpan();
  }

  *YieldStatement() {
    yield startSpan('Expression', '\n');
    yield eat(m`sigilToken*: <*Keyword 'yield' />`);
    yield eat(m`<__ExpressionList />`);
    yield endSpan();
  }

  *AwaitStatement() {
    yield startSpan('Expression', '\n');
    yield eat(m`sigilToken*: <*Keyword 'await' />`);
    yield eat(m`value$: <_Expression />`);
    yield endSpan();
  }

  *DeleteStatement() {
    yield eat(m`sigilToken*: <*Keyword 'del' />`);

    yield startSpan('Expression', '\n');
    yield eat(m`<__ExpressionList />`);
    yield endSpan();
  }

  *RaiseStatement({ props }) {
    yield startSpan('Expression', '\n');
    yield eat(m`sigilToken: <*Keyword 'raise' />`);
    yield eatMatch(m`expression+$: <_Expression />`);
    yield endSpan();
  }

  *PassStatement({ props }) {
    yield eat(m`sigilToken*: <*Keyword 'pass' />`);
  }

  *FunctionDefinition({ s, props }) {
    let { indent = null } = props;
    yield startSpan('Expression', m`/[:\n]/`);
    yield eat(m`sigilToken: <*Keyword 'def' />`);
    yield eat(m`name: <*Identifier />`);

    yield eat(m`openArgumentsToken*: <* '(' />`);
    yield startSubspan(null, ')');

    while (yield match(m`/./`)) {
      yield startSubspan(null, ',');
      yield eat(m`params[]+: <_Parameter />`);
      yield endSpan();
      yield eatMatch(m`#separatorToken: <* ',' />`);
    }

    yield endSpan();
    yield eat(m`closeArgumentsToken*: <* ')' />`);

    yield endSpan();
    yield eat(m`bodyToken: <* ':' />`);
    yield eat(m`#: <* '\n' />`);

    let { node: block } = yield eat(m`body$: <Block />`, o({ indent }));

    if (isEmpty(list('statements', block))) {
      yield fail();
    }
  }

  *GeneratorExpression() {
    yield eat(m`item+$: <_Expression />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken: <*Keyword 'for' />`);
    yield eat(m`pattern+: <_Pattern />`);
    yield eat(m`inToken: <*Keyword 'in' />`);
    yield eat(m`sequence+$: <_Expression />`);
  }

  *EmptyStatement() {}

  *IfStatement({ props }) {
    let { indent = null } = props;

    yield startSpan('Expression', '\n');
    yield startSpan('Expression', m`/\n|:/`);
    yield eat(m`sigilToken: <*Keyword 'if' />`);

    yield eat(m`condition+$: <_Expression />`);

    yield endSpan();
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`#: <* '\n' />`);

    yield eat(m`consequence: <Block />`, o({ indent }));

    while (yield match(m`/${indent}(?:elif|else)/`, o({ indent }))) {
      yield eat(m`#indent: <* '${indent}' />`);
      yield eat(m`alternatives[]: <_Alternative />`, o({ indent }));
    }
  }

  *Alternative({ props }) {
    if (yield eatMatch(m`<ElifClause 'elif' />`, o(props))) {
    } else {
      yield eatMatch(m`<ElseClause 'else' />`, o(props));
    }
  }

  *ElifClause({ props }) {
    let { indent = null } = props;

    yield startSpan('Expression', '\n');
    yield startSpan('Expression', m`/\n|:/`);
    yield eat(m`sigilToken: <*Keyword 'elif' />`);
    yield eat(m`condition+$: <_Expression />`);
    yield endSpan();
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`#: <* '\n' />`);

    yield eat(m`consequence: <Block />`, o({ indent }));
  }

  *ElseClause({ props }) {
    let { indent = null } = props;

    yield startSpan('Expression', '\n');
    yield startSpan('Expression', m`/\n|:/`);
    yield eat(m`sigilToken: <*Keyword 'else' />`);
    yield endSpan();
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`#: <* '\n' />`);

    yield eat(m`consequence: <Block />`, o({ indent }));
  }

  *ListComprehension({ p }) {
    yield eat(m`body+$: <_Expression />`, o({}), o({ held: 'eat' }));

    yield eat(m`clauses[]: <ForInClause />`);

    let clause;
    do {
      if ((clause = yield eat(m`clauses[]: <ForInClause />`))) {
      } else {
        clause = yield eat(m`clauses[]: <IfClause />`);
      }
    } while (clause);
  }

  *Pattern({ s }) {
    if (s().shifted) {
      yield eat(m`<PatternList />`);
    } else {
      yield eat(m`<*Identifier />`);

      return r(shiftMatch(m`<_Pattern ',' />`));
    }
  }

  *PatternList() {
    yield eat(m`patterns[]+$: <*Identifier />`, o({}), o({ held: 'eat' }));

    while (yield eatMatch(m`#separatorTokens: <* ',' />`)) {
      yield eatMatch(m`patterns[]+$: <*Identifier />`);
    }
  }

  *ForInClause() {
    let { powers: p } = this.constructor.context;

    yield eat(m`item+$: <_Expression />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken: <*Keyword 'for' />`);
    yield eat(m`pattern+: <_Pattern />`);
    yield eat(m`inToken: <*Keyword 'in' />`);
    yield eat(m`sequence+$: <_Expression />`);
  }

  *IfClause() {
    let { powers: p } = this.constructor.context;

    yield eat(m`consequence+$: <_Expression />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken: <*Keyword 'if' />`);
    yield eat(m`condition+$: <_Expression />`);
  }

  *Ellipsis() {
    yield eat('...');
  }

  *AssignmentExpression() {
    let { powers: p } = this.constructor.context;

    yield eat(m`left+$: <_Expression />`, o({ power: p.access }), o({ held: 'eat' }));
    yield eat(
      m`assignmentOperator*: <* ${printStreamSource(
        writePattern(assignmentOperatorAlternatives),
      )} />`,
    );
    yield eat(m`right+$: <_Expression />`, o({ power: p.assign }));
  }

  *CallExpression() {
    yield eat(m`callee+$: <_Expression />`, o({}), o({ held: 'eat' }));

    yield eat(m`openArgumentsToken*: <* '(' />`);
    yield startSpan('Bare', ')');
    let first = true;
    let arg = null;
    while ((first || get('separatorToken', arg.node)) && !(yield match(m`/$/`))) {
      arg = yield eat(m`arguments[]+$: <Argument />`);

      if (first) {
        yield startSpan('Expression', '\n');
        yield shiftMatch(m`<GeneratorExpression 'for' />`);
        yield endSpan();
      }
      first = false;
    }
    yield endSpan();
    yield eat(m`closeArgumentsToken*: <* ')' />`);
  }

  *Argument() {
    yield startSubspan(null, ',');
    yield eat(m`value+: <_Expression />`);
    yield endSpan();
    yield eatMatch(m`separatorToken*: <* ',' />`);
  }

  *Identifier() {
    let str = printSource(yield eat(m`/[a-zA-Z_]+/`));

    if (arrayIncludes(reservedWords, str)) {
      yield fail();
    }
  }

  *Parameter({ s }) {
    if (s().shifted) {
      yield eat(m`<DefaultParameter />`);
    } else {
      yield eat(m`_: <*Identifier />`);
      return r(shiftMatch(m`<_Parameter '=' />`));
    }
  }

  *DefaultParameter() {
    yield eat(m`name+$: <*Identifier />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken*: <* '=' />`);
    yield eat(m`value+$: <_Expression />`);
  }

  *Block({ props }) {
    yield eat(m`<__StatementList />`, o(props));
  }

  *Expression({ props: { power, noIn = false }, getState }) {
    let s = getState();
    let spanStarted = s.span.name === 'Expression';
    if (!spanStarted) {
      yield startSpan('Expression', '\n');
    }
    let { powers } = this.constructor.context;
    let power_ = power || powers.assign;
    let res;
    if (!s.shifted) {
      if ((res = yield eatMatch(m`<ParenthesisExpression '(' />`))) {
      } else if ((res = yield eatMatch(m`<_LiteralExpression />`))) {
      } else if (
        (res = yield eatMatch(
          m`<UnaryExpression ${printStreamSource(
            writePattern(unaryPrefixOperatorAlternatives),
          )} />`,
        ))
      ) {
      } else if ((res = yield eatMatch(m`<*Identifier ${startsIdentifierPattern} />`))) {
      }
    } else {
      res = yield eat(m`<_LogicExpression />`, o({ power: power_, noIn }));
    }

    if (!spanStarted) {
      yield endSpan();
    }

    if (res && !(yield match(m`/$/`))) {
      // TODO get the power-specific guard so this can not-branch
      return r(shiftMatch(m`<_Expression />`, o({ power: power_ })));
    }
  }

  *UnaryExpression({ literalValue, props: { op = printSource(literalValue) }, s }) {
    yield eat(
      m`sigilToken*: <*${op && /[a-z]/.test(op[0]) ? 'Keyword' : ''} ${printStreamSource(
        writePattern(unaryPrefixOperatorAlternatives),
      )} />`,
    );

    yield eat(m`argument+$: <_Expression />`);
  }

  *ComparisonExpression({ props: { op } }) {
    let { powers: p } = this.constructor.context;
    let power = powers.compare;

    yield startSpan('Expression', '\n');
    yield eat(m`expressions[]+$: <_Expression />`, o({ power: power - 1 }), o({ held: 'eat' }));

    let first = true;
    while (true) {
      if (!op) {
        op = printSource(
          yield match(
            buildEmbeddedRegexMatcher(
              printStreamSource(writePattern(getBinaryOperatorAlternatives(p, power))),
            ),
          ),
        );
      }

      if (!op) {
        if (first) {
          yield fail();
        } else {
          break;
        }
      }

      yield eat(
        m`operators[]*: <*${
          ['in', 'not in', 'is', 'is not'].includes(op) ? 'Keyword' : ''
        } ${printString(op)} />`,
      );

      yield eat(m`expressions[]+$: <_Expression />`, o({ power: power - 1 }));
      op = null;
      first = false;
    }
    yield endSpan();
  }

  *BinaryExpression({ props: { op, power } }) {
    let { powers: p } = this.constructor.context;

    yield startSubspan('Expression', '\n');
    yield eat(m`left+$: <_Expression />`, o({ power: power - 1 }), o({ held: 'eat' }));

    if (!op) {
      op = printSource(
        yield match(
          buildEmbeddedRegexMatcher(
            printStreamSource(writePattern(getBinaryOperatorAlternatives(p, power))),
          ),
        ),
      );
    }

    yield eat(
      m`sigilToken*: <*${['not', 'and', 'or'].includes(op) ? 'Keyword' : ''} ${printString(op)} />`,
    );

    let ownPower = getBinaryOperatorPower(p, op);

    yield eat(m`right+$: <_Expression />`, o({ power: ownPower - 1 }));
    yield endSpan();
  }

  *LiteralExpression() {
    let res = yield match(m`/(?:True|False|None|def|lambda)\b|[[('"{\d]/`);

    switch (printSource(res)) {
      case null:
        break;
      case 'True':
      case 'False':
        yield eat(m`<Boolean />`);
        break;
      case 'None':
        yield eat(m`<None />`);
        break;
      case 'lambda':
        yield eat(m`<Lambda />`);
        break;
      case 'def':
        yield eat(m`<FunctionDefinition />`);
        break;
      case "'":
      case '"':
        yield eat(m`<String />`);
        break;
      case '{':
        yield eat(m`<Dictionary />`);
        break;
      case '[':
        yield eat(m`<Array />`);
        break;
      case '(':
        yield eat(m`<Tuple />`);
        break;
      default:
        yield eat(m`<Number /[-\d]/ />`);
        break;
    }
  }

  *Boolean() {
    yield eat(m`sigilToken*: <*Keyword /True|False/ />`);
  }

  *None() {
    yield eat(m`sigilToken*: <*Keyword 'None' />`);
  }

  *String() {
    let q = yield match(m`/['"]/`);

    if (!q) yield fail();

    const q_ = printSource(q);

    let span = q_ === "'" ? 'String:Single' : 'String:Double';
    yield startSpan(span, q_);
    yield q_ === "'" ? eat(m`openToken*: <* "'" />`) : eat(m`openToken*: <* '"' />`);
    yield eat(m`content$: <*StringContent />`);
    yield q_ === "'" ? eat(m`closeToken*: <* "'" />`) : eat(m`closeToken*: <* '"' />`);
    yield endSpan();
  }

  *StringContent({ s }) {
    let esc, lit;
    do {
      lit =
        s().span.name === 'String:Single'
          ? yield eatMatch(m`/[^\r\n\\']+/`)
          : yield eatMatch(m`/[^\r\n\\"]+/`);
      // esc = yield eatMatch(m`<EscapeSequence '\\' />`, o({}), o({ escape: true }));
    } while (esc || lit);
  }

  *UnsignedInteger({ props: { noDoubleZero = false } }) {
    let firstDigit = printSource(yield eat(m`/\d/`));

    if (!noDoubleZero || firstDigit.value !== '0') {
      yield eatMatch(m`/\d+/`);
    }
  }

  *UnsignedHexInteger() {
    yield eatMatch(m`/0x[\da-fA-F]+/`);
  }

  *Number() {
    yield startSpan('Number');

    yield eatMatch(m`sign*: <* /[+-]/ />`);

    if (yield match(m`'0x'`)) {
      yield eat(m`wholePart$: <*UnsignedHexInteger />`);
      yield endSpan();
      return;
    } else {
      yield eat(m`wholePart$: <*UnsignedInteger />`, o({ noDoubleZero: true }));
    }

    let fs = yield eatMatch(m`fractionalSeparatorToken*: <* '.' />`);

    if (fs) {
      yield eat(m`decimalPart$: <*UnsignedInteger />`);
    } else {
      yield eat(m`decimalPart$: null`);
    }

    let es = yield eatMatch(m`exponentSeparator*: <* /[eE]/ />`);

    if (es) {
      yield eat(m`exponentPart$: <Integer />`, { matchSign: /[+-]/ });
    } else {
      yield eat(m`exponentPart$: null`);
    }
    yield endSpan();
  }

  *ParenthesisExpression() {
    yield eat(m`openToken*: <* '(' />`);
    yield startSpan('Bare', ')');
    yield eat(m`expression+$: <_Expression />`);
    yield endSpan();
    yield eat(m`closeToken*: <* ')' />`);
  }

  *MemberExpression() {
    let { powers: p } = this.constructor.context;

    yield eat(m`object+$: <_Expression />`, o({ power: p.exponent }), o({ held: 'eat' }));
    let sigil = yield match(m`/[[.]/`);
    switch (printSource(sigil)) {
      case '.': {
        yield eat(m`dotToken*: <* '.' />`);
        yield eat(m`property+$: <*Identifier />`, o({ scoped: false }));
        break;
      }

      case '[': {
        yield eat(m`openToken*: <* '[' />`);
        yield startSpan('Bare', ']');
        yield eat(m`property+$: <_Expression />`);
        yield endSpan();
        yield eat(m`closeToken*: <* ']' />`);
        break;
      }

      default:
        yield fail();
    }
  }

  *LogicExpression({ language, s, props: { power, noIn = false } }) {
    let { shifted } = s();
    if (!shifted) return;
    let { powers: p } = this.constructor.context;

    let op = yield match(
      m`/[[.(?]|==|for|if|${printStreamSource(
        writeRegexGroup(assignmentOperatorAlternatives),
      )}|${printStreamSource(writeRegexGroup(getBinaryOperatorAlternatives(p, power)))}/`,
    );

    if (!op) return;

    op = printSource(op);

    let res;
    if (['.', '['].includes(op)) {
      res = yield eat(m`<MemberExpression />`, o({ power }));
    }
    if (!res && op == '(') {
      if (shifted) {
        res = yield eat(m`<CallExpression />`, o({ power }));
      } else {
        res = yield eat(m`<ParenthesisExpression />`, o({ power }));
      }
    }

    if (!res) {
      for (let powerRank of arraySlice(binaryExpressionPowerRank, 0, power)) {
        if (arrayIncludes(powerRank, op)) {
          if (powerRank === binaryExpressionPowerRank[powers.compare]) {
            res = yield eatMatch(m`<ComparisonExpression />`);
          } else {
            res = yield eatMatch(m`<BinaryExpression />`, o({ op, power, noIn }));
          }
          break;
        }
      }
    }
    if (!res && power >= p.assign) {
      if (
        arrayIncludes(language.context.assignables, getRoot(shifted).value.name.description) &&
        arrayIncludes(assignmentOperators, op) &&
        (res = yield eat(m`<AssignmentExpression />`, o({ power })))
      ) {
      }
    }
  }

  *Lambda() {
    yield eat(m`sigilToken*: <*Keyword 'lambda' />`);

    yield startSpan('Expression', ':');
    while (yield match(m`/./`)) {
      yield startSubspan(null, ',');
      yield eat(m`params[]+: <_Parameter />`);
      yield endSpan();
      yield eatMatch(m`#separatorToken: <* ',' />`);
    }
    yield endSpan();

    yield eat(m`bodyToken*: <* ':' />`);
    yield eat(m`body+$: <_Expression />`);
  }

  *Dictionary() {
    yield eat(m`openToken*: <* '{' />`);

    yield startSpan('Expression', '}');

    let keyed = null;
    while (yield match(m`/./`)) {
      let entry = yield eat(m`entries[]+: <_DictionaryEntry />`);
      if (keyed === null) {
        keyed = getRoot(entry.node).type === Symbol.for('Pair');
        yield defineAttribute('keyed', keyed);
      }
      yield eatMatch(m`#separatorToken: <* ',' />`);
    }

    if (keyed === null) {
      keyed = true;
      yield defineAttribute('keyed', keyed);
    }

    yield endSpan();

    yield eat(m`closeToken*: <* '}' />`);
  }

  *Array() {
    yield eat(m`openToken*: <* '[' />`);

    yield startSpan('Expression', ']');
    while (yield match(m`/./`)) {
      yield startSubspan(null, ',');
      yield eat(m`elements[]+: <_Expression />`);
      yield endSpan();
      yield eatMatch(m`#separatorToken: <* ',' />`);
    }
    yield endSpan();

    yield eat(m`closeToken*: <* ']' />`);
  }

  *Tuple() {
    yield eat(m`openToken*: <* '(' />`);

    yield startSpan('Expression', ')');
    while (yield match(m`/./`)) {
      yield startSubspan(null, ',');
      yield eat(m`elements[]+: <_Expression />`);
      yield endSpan();
      yield eatMatch(m`#separatorToken: <* ',' />`);
    }
    yield endSpan();

    yield eat(m`closeToken*: <* ')' />`);
  }

  *DictionaryEntry({ s }) {
    if (s().shifted) {
      yield eat(m`<Pair />`);
    } else {
      yield eat(m`_: <*String />`);
      return r(shiftMatch(m`<_DictionaryEntry ':' />`));
    }
  }

  *Pair() {
    yield eat(m`key+$: <*String />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken*: <* ':' />`);
    yield eat(m`value+$: <_Expression />`);
  }
}

freezeClass(PythonGrammarAtrivial);

export default triviaEnhancer(
  {
    triviaIsAllowed: (s) => s.span.name === 'Expression',

    *Trivia({ s }) {
      yield eatMatch(m`#: <* /[ \t]+/ />`, o({}), o({ hold: true }));
    },
  },
  PythonGrammarAtrivial,
);
