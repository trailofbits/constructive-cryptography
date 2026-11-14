#!/usr/bin/env ruby
# Check the same required sections locally and in the issues workflow.
require "yaml"

forms = Dir[File.expand_path("../.github/ISSUE_TEMPLATE/*.yml", __dir__)].map do |file|
  fields = YAML.safe_load(File.read(file))["body"]
  [File.basename(file, ".yml"), fields.map { |f| f.fetch("attributes").fetch("label") }] if fields
end.compact.to_h

kind, file = ARGV
unless ARGV.length == 2 && (kind == "auto" || forms.key?(kind))
  abort "Usage: #{$PROGRAM_NAME} {#{(forms.keys + ['auto']).join('|')}} BODY.md"
end

# Ignore prompts and treat headings inside fenced code or math as content.
body = File.read(file).gsub(/<!--.*?(?:-->|\z)/m, "")
sections = []
fence = nil
body.each_line do |line|
  text = line.strip
  if fence
    if text.match?(/\A#{Regexp.escape(fence[0])}{#{fence.size},}\z/)
      fence = nil
      next
    end
  elsif (match = line.match(/^ {0,3}(`{3,}|~{3,})/))
    fence = match[1]
    next
  elsif (heading = line.match(/^###\s+(.+?)\s*$/))
    sections << [heading[1], false]
    next
  end
  if !sections.empty? && !text.empty? && text != "_No response_"
    sections.last[1] = true
  end
end

allowed = kind == "auto" ? forms.values : [forms.fetch(kind)]
unless allowed.include?(sections.map(&:first))
  warn "Expected headings: " + allowed.map { |labels| labels.join(" / ") }.join(" or ")
  exit 2
end
empty = sections.reject(&:last).map(&:first)
unless empty.empty?
  warn "Fill in: #{empty.join(', ')}"
  exit 2
end
