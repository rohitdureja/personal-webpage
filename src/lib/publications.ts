import { readFileSync } from 'node:fs';
import { join } from 'node:path';

export type PublicationType =
  | 'inproceedings'
  | 'article'
  | 'misc'
  | 'book'
  | 'thesis';

export type Publication = {
  key: string;
  type: PublicationType;
  bibtex: string;
  order: number;
  author?: string;
  title?: string;
  booktitle?: string;
  journal?: string;
  publisher?: string;
  year?: string;
  url?: string;
  abstract?: string;
  preprint?: string;
  slides?: string;
  website?: string;
  poster?: string;
  pdf?: string;
  award?: string;
};

const bibliographySource = readFileSync(
  join(process.cwd(), '_bibliography', 'references.bib'),
  'utf8'
);

function splitEntries(source: string) {
  const entries: string[] = [];
  let i = 0;

  while (i < source.length) {
    const atIndex = source.indexOf('@', i);
    if (atIndex === -1) break;

    const braceIndex = source.indexOf('{', atIndex);
    if (braceIndex === -1) break;

    let depth = 0;
    let endIndex = braceIndex;

    for (; endIndex < source.length; endIndex += 1) {
      const char = source[endIndex];
      if (char === '{') depth += 1;
      if (char === '}') {
        depth -= 1;
        if (depth === 0) {
          entries.push(source.slice(atIndex, endIndex + 1).trim());
          i = endIndex + 1;
          break;
        }
      }
    }
  }

  return entries;
}

function splitTopLevel(input: string) {
  const parts: string[] = [];
  let current = '';
  let depth = 0;
  let quote = false;

  for (let i = 0; i < input.length; i += 1) {
    const char = input[i];
    const previous = input[i - 1];

    if (char === '"' && previous !== '\\') {
      quote = !quote;
    }

    if (!quote) {
      if (char === '{') depth += 1;
      if (char === '}') depth -= 1;
    }

    if (char === ',' && depth === 0 && !quote) {
      if (current.trim()) parts.push(current.trim());
      current = '';
      continue;
    }

    current += char;
  }

  if (current.trim()) parts.push(current.trim());
  return parts;
}

function unwrapValue(value: string) {
  const trimmed = value.trim();

  if (
    (trimmed.startsWith('{') && trimmed.endsWith('}')) ||
    (trimmed.startsWith('"') && trimmed.endsWith('"'))
  ) {
    return trimmed.slice(1, -1).trim();
  }

  return trimmed;
}

function sanitizeDisplayText(value: string) {
  return value
    .replace(/[{}]/g, '')
    .replace(/\\_/g, '_')
    .replace(/\s+/g, ' ')
    .trim();
}

function parseEntry(entrySource: string, order: number): Publication | null {
  const headerMatch = entrySource.match(/^@(\w+)\s*\{\s*([^,]+),([\s\S]*)\}$/);
  if (!headerMatch) return null;

  const [, rawType, rawKey, rawBody] = headerMatch;
  const type = rawType.toLowerCase() as PublicationType;
  const key = rawKey.trim();
  const fields = splitTopLevel(rawBody.trim().replace(/,\s*$/, ''));

  const publication: Publication = {
    key,
    type,
    bibtex: entrySource,
    order
  };

  for (const field of fields) {
    const separatorIndex = field.indexOf('=');
    if (separatorIndex === -1) continue;

    const fieldName = field.slice(0, separatorIndex).trim().toLowerCase();
    const fieldValue = unwrapValue(field.slice(separatorIndex + 1));
    const displayFields = new Set([
      'author',
      'title',
      'booktitle',
      'journal',
      'publisher',
      'abstract',
      'award'
    ]);
    const normalizedValue = displayFields.has(fieldName)
      ? sanitizeDisplayText(fieldValue)
      : fieldValue;

    publication[fieldName as keyof Publication] = normalizedValue as never;
  }

  return publication;
}

function comparePublications(a: Publication, b: Publication) {
  const yearA = Number.parseInt(a.year ?? '0', 10);
  const yearB = Number.parseInt(b.year ?? '0', 10);

  if (yearA !== yearB) {
    return yearB - yearA;
  }

  return a.order - b.order;
}

const publications = splitEntries(bibliographySource)
  .map((entry, index) => parseEntry(entry, index))
  .filter((entry): entry is Publication => Boolean(entry))
  .sort(comparePublications);

const sectionDefinitions: Array<{
  title: string;
  types: PublicationType[];
}> = [
  { title: 'Peer Reviewed Conferences', types: ['inproceedings'] },
  { title: 'Journals', types: ['article'] },
  { title: 'Theses', types: ['thesis'] },
  { title: 'Workshops and Posters', types: ['misc'] },
  { title: 'Books and Book Chapters', types: ['book'] }
];

export const publicationSections = sectionDefinitions
  .map((section) => ({
    ...section,
    items: publications.filter((publication) => section.types.includes(publication.type))
  }))
  .filter((section) => section.items.length > 0);

export function getPublications() {
  return publications;
}

export function getPublicationByKey(key: string) {
  return publications.find((publication) => publication.key === key);
}

export function formatAuthors(authorField = '') {
  const authors = authorField
    .split(/\s+and\s+/i)
    .map((author) => author.trim())
    .filter(Boolean)
    .map((author) => {
      if (!author.includes(',')) return author;
      const [last, first] = author.split(',').map((part) => part.trim());
      return `${first} ${last}`.trim();
    });

  if (authors.length <= 2) {
    return authors.join(' and ');
  }

  return `${authors.slice(0, -1).join(', ')}, and ${authors.at(-1)}`;
}

export function publicationVenue(publication: Publication) {
  if (publication.booktitle) return publication.booktitle;
  if (publication.journal) return publication.journal;
  if (publication.publisher) return publication.publisher;
  return '';
}

export function normalizeAssetPath(path?: string) {
  if (!path) return undefined;
  if (path.startsWith('http://') || path.startsWith('https://') || path.startsWith('/')) {
    return path;
  }

  return `/${path.replace(/^(\.\.\/)+/, '')}`;
}
