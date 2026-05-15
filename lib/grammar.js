import { freeze, freezeClass, freezeRecord } from '@bablr/agast-helpers/object';
import { get, getRoot } from '@bablr/agast-helpers/path';
import * as BSet from '@bablr/agast-helpers/b-set';
import * as BMap from '@bablr/agast-helpers/b-map';
import {
  eat,
  eatMatch,
  endSpan,
  fail,
  m,
  match,
  o,
  r,
  shiftMatch,
  startSpan,
} from '@bablr/helpers/grammar';
import { printSource } from '@bablr/agast-helpers/tree';
import { printSource as printStreamSource } from '@bablr/agast-helpers/stream';
import { writePattern, writeRegexGroup } from '@bablr/helpers/builders';
import { arrayValues, flatMap } from '@bablr/agast-helpers/iterable';
import { triviaEnhancer } from '@bablr/helpers/trivia';
import Space from '@bablr/language-en-blank-space';
import { startsIdentifierPattern } from './util.js';

let { includes, slice } = Array.prototype;

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
  do: m`<DoWhile />`,
  switch: m`<Switch />`,
  for: m`<For />`,
  def: m`<FunctionDefinition />`,
  try: m`<TryCatch />`,
  return: m`<ReturnStatement />`,
  continue: m`<Continue />`,
  break: m`<Break />`,
  raise: m`<RaiseStatement />`,
  pass: m`<PassStatement />`,
  elif: m`<ElifClause />`,
  else: m`<ElseClause />`,
};

let powers = freezeRecord({
  assign: 15,
  logical_or: 14,
  logical_and: 13,
  bitwise_or: 12,
  bitwise_xor: 11,
  bitwise_and: 10,
  equals: 9,
  compare: 8,
  bitwise_shift: 7,
  add: 6,
  multiply: 5,
  unary_prefix: 4,
  call: 2,
  access: 0,
});

const buildOperatorAlternatives = (categories) =>
  freezeRecord([...flatMap((operators) => arrayValues(operators), arrayValues(categories))]);

export const assignmentOperators = freezeRecord([
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
    Array.prototype.slice.call(binaryExpressionPowerRank, Math.max(0, powers.logical_or - power)),
  );
};

const getBinaryOperatorPower = (p, str) => {
  let idx = Array.prototype.findIndex.call(binaryExpressionPowerRank, (arr) =>
    includes.call(arr, str),
  );
  return idx >= 0 ? p.logical_or - idx : null;
};

let binaryExpressionMatchers = new Map();
let logicExpressionMatchers = new Map();
let assignmentMatcher;

const binaryExpressionPowerRank = freezeRecord([
  freezeRecord(['||']),
  freezeRecord(['&&']),
  freezeRecord(['|']),
  freezeRecord(['^']),
  freezeRecord(['&']),
  freezeRecord(['==', '!=']),
  freezeRecord(['<=', '<', '>=', '>']),
  freezeRecord(['<<', '>>']),
  freezeRecord(['+', '-']),
  freezeRecord(['%', '*', '/']),
]);

export const unaryPrefixOperators = freezeRecord(['+', '-', '!', '~']);
export const unaryPrefixOperatorAlternatives = buildOperatorAlternatives([unaryPrefixOperators]);

let assignables = freezeRecord(['MemberExpression', 'Identifier']);

class PythonGrammarAtrivial {
  static canonicalURL = 'https://bablr.org/languages/universe/en/python';
  static dependencies = freeze({ Space });
  static defaultMatcher = m`_+: <_Expression />`;
  static fragmentProduction = 'Fragment';
  static context = freezeRecord({ powers, assignables });

  constructor() {
    this.literals = BSet.from('Keyword');
    this.emptyables = BSet.add('StringContent', this.emptyables || BSet.create());
  }

  *Module() {
    yield eat(m`<__StatementList />`);
  }

  *StatementList() {
    let first = true;
    let newline = null;
    while (first || newline) {
      yield eatMatch(m`statements[]: <_Statement />`);
      newline = yield eatMatch(m`#statementSeparator: <* '\n' />`);
      first = false;
    }
  }

  *Statement({ getState }) {
    let s = getState();
    let res;
    if (s.source.done) {
      return;
    } else {
      yield startSpan('Statement', m`/\n|\r\n|\r/`);
      if (
        (res = yield match(
          m`/(?:if|elif|else|while|do|switch|for|def|try|return|continue|break|raise|pass)\b/`,
        ))
      ) {
        yield eat(productions[printSource(res)]);
      } else {
        yield eat(m`<ExpressionStatement />`);
      }
      yield endSpan();
    }
  }

  *ExpressionStatement() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`expression+$: <_Expression />`);
    yield endSpan();
  }

  *ReturnStatement() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`sigilToken*: <*Keyword 'return' />`);
    yield eatMatch(m`expression+$: <_Expression />`);
    yield endSpan();
  }

  *RaiseStatement() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`sigilToken: <*Keyword 'raise' />`);
    yield eatMatch(m`expression+$: <_Expression />`);
    yield endSpan();
  }

  *PassStatement() {
    yield eat(m`sigilToken*: <*Keyword 'pass' />`);
  }

  *FunctionDefinition() {
    yield eat(m`sigilToken: <*Keyword 'def' />`);
    yield eat(m`name: <*Identifier />`);
    yield eat(m`openArgumentsToken*: <* '(' />`);

    let sep = true;
    while (sep && !(yield match(m`/$/`))) {
      // arg = yield eat(m`arguments[]+$: <Argument />`);

      yield eat(m`params[]+: <_Parameter />`);

      sep = yield eatMatch(m`#separatorToken: <* ',' />`);
    }

    yield eat(m`closeArgumentsToken*: <* ')' />`);
    yield eat(m`bodyToken: <* ':' />`);
    yield eat(m`body$: <__StatementList />`);
  }

  *IfStatement() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`sigilToken: <*Keyword 'if' />`);
    yield eat(m`expression+$: <_Expression />`);
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`consequence: <Block />`);

    while (yield eatMatch(m`alternatives[]: <_Alternative /elif|else/ />`)) {}
  }

  *Alternative() {
    if (yield eatMatch(m`<ElifClause 'elif' />`)) {
    } else {
      yield eatMatch(m`<ElseClause 'else' />`);
    }
  }

  *ElifClause() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`sigilToken: <*Keyword 'elif' />`);
    yield eat(m`expression+$: <_Expression />`);
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`consequence: <Block />`);
  }

  *ElseClause() {
    yield startSpan('Statement', m`/\n|\r\n|\r/`);
    yield eat(m`sigilToken: <*Keyword 'else' />`);
    yield eat(m`expression+$: <_Expression />`);
    yield eat(m`consequenceBodyToken: <* ':' />`);
    yield endSpan();

    yield eat(m`consequence: <Block />`);
  }

  *Ellipsis() {
    yield eat('...');
  }

  *AssignmentExpression() {
    let { powers: p } = this.constructor.context;
    yield eat(m`left+$: <_Expression />`, o({ power: p.access }), o({ held: 'eat' }));
    assignmentMatcher ??= m`assignmentOperator*: <* ${printStreamSource(
      writePattern(assignmentOperatorAlternatives),
    )} />`;
    yield eat(assignmentMatcher);
    yield eat(m`right+$: <_Expression />`, o({ power: p.assign }));
  }

  *CallExpression() {
    yield eat(m`callee+$: <_Expression />`, o({}), o({ held: 'eat' }));

    yield eat(m`openArgumentsToken*: <* '(' />`);
    yield startSpan('Bare', ')');
    let arg = true;
    while ((arg === true || get('separatorToken', arg.node)) && !(yield match(m`/$/`))) {
      arg = yield eat(m`arguments[]+$: <Argument />`);
    }
    if (arg && get('separatorToken', arg.node)) yield fail();
    yield endSpan();
    yield eat(m`closeArgumentsToken*: <* ')' />`);
  }

  *Argument() {
    yield eat(m`value+: <_Expression />`);
    yield eatMatch(m`separatorToken*: <* ',' />`);
  }

  *Identifier() {
    yield eat(m`/[a-zA-Z_]+/`);
  }

  *Parameter({ s }) {
    if (s().held) {
      yield eat(m`<DefaultParameter />`);
    } else {
      yield eat(m`_: <*Identifier />`);
    }

    return r(shiftMatch(m`<Parameter '=' />`));
  }

  *DefaultParameter() {
    yield eat(m`name+$: <*Identifier />`, o({}), o({ held: 'eat' }));
    yield eat(m`sigilToken*: <* '=' />`);
    yield eat(m`value+$: <_Expression />`);
  }

  *Block() {
    yield eat(m`<__StatementList />`);
  }

  *ParenthesisExpression() {
    yield eat(m`openToken*: <* '(' />`);
    yield startSpan('Bare', ')');
    yield eat(m`expression+$: <_Expression />`);
    yield endSpan();
    yield eat(m`closeToken*: <* ')' />`);
  }

  *Expression({ props: { power, noIn = false }, s }) {
    let { powers } = this.constructor.context;
    let power_ = power || powers.assign;
    let res;
    if (!s().shifted) {
      if ((res = yield eatMatch(m`<ParenthesisExpression '(' />`))) {
      } else if ((res = yield eatMatch(m`<_LiteralExpression />`))) {
      } else if ((res = yield eatMatch(m`<FunctionDefinition 'def' />`))) {
      } else if (
        power_ >= powers.unary_prefix &&
        (res = yield eatMatch(
          m`<UnaryExpression ${printStreamSource(
            writePattern(unaryPrefixOperatorAlternatives),
          )} />`,
        ))
      ) {
      } else if (
        power_ >= powers.new &&
        (res = yield eatMatch(m`<NewExpression 'new' />`, o({ power: power_ })))
      ) {
      } else if ((res = yield eatMatch(m`<*Identifier ${startsIdentifierPattern} />`))) {
      }
    } else {
      res = yield eat(m`<_LogicExpression />`, o({ power: power_, noIn }));
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

  *BinaryExpression({ props: { op, power } }) {
    let { powers: p } = this.constructor.context;
    yield eat(m`left+$: <_Expression />`, o({ power: power - 1 }), o({ held: 'eat' }));

    let matcherCache = binaryExpressionMatchers;
    let pattern = matcherCache.get(power);

    if (!op) {
      op = printSource(
        yield match(printStreamSource(writePattern(getBinaryOperatorAlternatives(p, power)))),
      );
    }

    pattern ??= printStreamSource(writePattern(getBinaryOperatorAlternatives(p, power)));

    matcherCache.set(power, pattern);

    yield eat(
      m`sigilToken*: <*${['instanceof', 'in'].includes(op) ? 'Keyword' : ''} ${pattern} />`,
    );

    let ownPower = getBinaryOperatorPower(p, op);

    yield eat(m`right+$: <_Expression />`, o({ power: ownPower - 1 }));
  }

  *LiteralExpression() {
    let res = yield match(m`/(?:True|False|None)\b|['"\d]/`);

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
      case "'":
      case '"':
        yield eat(m`<String />`);
        break;
      default:
        yield eat(m`<Number /\d/ />`);
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
      // esc = yield eatMatch(m`@: <EscapeSequence '\\' />`);
    } while (esc || lit);
  }

  *UnsignedInteger({ props: { noDoubleZero = false } }) {
    let firstDigit = printSource(yield eat(m`/\d/`));

    if (!noDoubleZero || firstDigit.value !== '0') {
      yield eatMatch(m`/\d+/`);
    }
  }

  *Number() {
    yield startSpan('Number');
    yield eat(m`wholePart$: <*UnsignedInteger />`, o({ noDoubleZero: true }));

    let fs = yield eatMatch(m`fractionalSeparatorToken*: <* '.' />`);

    if (fs) {
      yield eat(m`decimalPart$: <*UnsignedInteger />`);
    } else {
      yield eat(m`decimalPart$: null`);
    }

    let es = yield eatMatch(m`exponentSeparatorToken*: <* /[eE]/ />`);

    if (es) {
      yield eat(m`exponentPart$: <Integer />`, { matchSign: /[+-]/ });
    } else {
      yield eat(m`exponentPart$: null`);
    }
    yield endSpan();
  }

  *LogicExpression({ language, s, props: { power, noIn = false } }) {
    let { shifted } = s();
    if (!shifted) return;
    let { powers: p } = this.constructor.context;

    let power_ = power;

    let matcherCache = logicExpressionMatchers;
    let matcher = matcherCache.get(power_);

    matcher ??= m`/[[.(?]|==|${printStreamSource(
      writeRegexGroup(assignmentOperatorAlternatives),
    )}|${printStreamSource(writeRegexGroup(getBinaryOperatorAlternatives(p, power_)))}/`;

    matcherCache.set(power_, matcher);

    let op = yield match(matcher);

    if (!op) return;

    op = printSource(op);

    let res;
    if (power_ >= p.access && ['.', '['].includes(op)) {
      res = yield eat(m`<MemberExpression />`, o({ power: power_ }));
    }
    if (!res && power_ >= p.call && op == '(') {
      res = yield eat(m`<CallExpression />`, o({ power: power_ }));
    }
    if (!res && power_ >= p.multiply) {
      for (let powerRank of slice.call(
        binaryExpressionPowerRank,
        Math.max(0, p.logical_or - power_),
      )) {
        if (includes.call(powerRank, op)) {
          res = yield eat(m`<BinaryExpression />`, o({ op, power: power_, noIn }));
        }
      }
    }
    if (!res && power_ >= p.assign) {
      if (
        includes.call(language.context.assignables, getRoot(shifted).value.name.description) &&
        includes.call(assignmentOperators, op) &&
        (res = yield eat(m`<AssignmentExpression />`, o({ power: power_ })))
      ) {
      } else if (op === '?' && (res = yield eat(m`<TernaryExpression />`, o({ power: power_ })))) {
      }
    }
  }

  *Trivia() {
    while (yield eatMatch(m`.: :Space: <_Blank /[ \n\r\t]+/ />`));
  }
}

freezeClass(PythonGrammarAtrivial);

export default triviaEnhancer(
  {
    triviaIsAllowed: (s) => ['Bare', 'Statement'].includes(s.span.name),

    *Trivia({ s }) {
      let span = BMap.get('Trivia', s().spans);

      let spaces = span?.props.spaces ?? Infinity;

      let res = yield match(m`/[ \t][^ \t\r\n\g]|[ \n\r\t]/`);

      if (res) {
        res = printSource(res);

        yield startSpan('Trivia', null, span?.props);
        if (' \t'.includes(res[0]) && res.length === 2 && spaces > 1) {
          yield eat(m`#: <* ' ' />`, o({}), o({ hold: true }));
        } else {
          yield eat(m`#: <Trivia />`, o({}), o({ hold: true }));
        }
        yield endSpan();
      }
    },
  },
  PythonGrammarAtrivial,
);
