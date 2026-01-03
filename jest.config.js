import { createDefaultEsmPreset } from 'ts-jest';

export default {
  ...createDefaultEsmPreset(),
  testPathIgnorePatterns: ["<rootDir>/node_modules", "<rootDir>/dist"]
}
